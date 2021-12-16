use libcad::annot::AnnotFile;
use libcad::llir::interp::rtti::ExtIdent;
use libcad::llir::syntax::Module;
use libcad::typechk::{TypeChk, TypeChkReport};
use std::fs;
use std::path::Path;

fn read_file(path: &Path) -> String {
    fs::read_to_string(path).unwrap()
}

fn load_module_from_file(filename: &str) -> Module<ExtIdent> {
    let path = Path::new(env!("OUT_DIR")).join(filename);
    Module::parse(&read_file(&path), filename).unwrap()
}

fn typechk(filename: &str, annotname: Option<&str>) -> Result<TypeChkReport, String> {
    let annotfile = match annotname {
        Some(annotname) => {
            let path = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests")
                .join("annot")
                .join(annotname);
            AnnotFile::parse(&read_file(&path), String::from("annot"))?
        }
        None => AnnotFile::empty(),
    };
    let mut module = load_module_from_file(filename);
    let datalayout = module.target_datalayout().clone(); // Avoid borrowck.
    annotfile.rewrite_typedefs(module.typedefs_mut(), &datalayout)?;
    let mut typechk = TypeChk::new(&annotfile, &module)?;
    typechk.check_types()?;
    if !annotfile.is_empty() {
        typechk.check_casts()?;
    }
    Ok(typechk.report())
}

fn assert_typechk(
    filename: &str,
    annotname: Option<&str>,
    expected_castwarns: &[&str],
    expected_typewarns: &[&str],
) {
    let report = typechk(filename, annotname).unwrap();
    let mut nunsafe_casts = 0;
    for warn in report.castwarns {
        if warn.msg.is_valid() {
            continue;
        }
        let warnstr = format!("{}", warn);
        match expected_castwarns.get(nunsafe_casts) {
            Some(expected) => assert_eq!(expected, &warnstr),
            None => panic!("too many unsafe CastWarns: {}", warnstr),
        }
        nunsafe_casts += 1;
    }
    assert_eq!(
        expected_castwarns.len(),
        nunsafe_casts,
        "number of unsafe CastWarns unmatched"
    );
    let mut ntypewarns = 0;
    for warn in report.typewarns {
        let warnstr = format!("{}", warn);
        match expected_typewarns.get(ntypewarns) {
            Some(expected) => assert_eq!(expected, &warnstr),
            None => panic!("too many TypeWarns: {}", warnstr),
        }
        ntypewarns += 1;
    }
    assert_eq!(
        expected_typewarns.len(),
        ntypewarns,
        "number of TypeWarns ummatched"
    );
}

#[test]
fn test_pointer_subtyping_unsoundness() {
    assert_typechk(
        "pointer_subtyping_unsoundness.ll",
        None,
        &vec![],
        &vec!["./tests/cpp/pointer_subtyping_unsoundness.cpp:31:16(@main): *<?_>%struct.ColorPoint is not subtype of *<?_>%struct.Point"],
    );
}

#[test]
fn test_tagged_union() {
    assert_typechk(
        "tagged_union.ll",
        Some("tagged_union.lisp"),
        &vec![],
        &vec![
            "??(@_Z17use_object_allocav): *<?_>%struct.Object is allocated with alloca as containing extension types",
            "./tests/cpp/tagged_union.cpp:6:17(@_Z20object_alloc_bool_vti): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union.cpp:17:17(@_Z20object_alloc_byte_tvh): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union.cpp:25:17(@_Z20object_alloc_byte_vth): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union.cpp:33:17(@_Z20object_alloc_closureP7Closure): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union.cpp:83:21(@_Z25object_select_second_byteP6Objectm): non-zero index 16 from *<?_>%struct.Object",
            "./tests/cpp/tagged_union.cpp:84:20(@_Z25object_select_second_byteP6Objectm): non-zero index 16 from *<?_>%struct.Object",
        ],
    );
}

#[test]
fn test_tagged_union_vuln() {
    assert_typechk(
        "tagged_union_vuln.ll",
        Some("tagged_union.lisp"),
        &vec![
            "./tests/cpp/tagged_union_vuln.cpp:7:3(@_Z19object_alloc_byte_tv): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x3, deref($0)))",
            "./tests/cpp/tagged_union_vuln.cpp:14:12(@_Z19object_alloc_byte_vh): store i8 to *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(0x2a, deref($1)))",
            "./tests/cpp/tagged_union_vuln.cpp:21:3(@_Z20object_alloc_byte_tvh): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x8, deref($0)))",
            "./tests/cpp/tagged_union_vuln.cpp:22:12(@_Z20object_alloc_byte_tvh): store i8 to *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(0x2a, deref($1)), eq(0x8, deref($0)))",
            "./tests/cpp/tagged_union_vuln.cpp:29:3(@_Z21object_alloc_byte_txvh): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x3, deref($0)))",
            "./tests/cpp/tagged_union_vuln.cpp:31:12(@_Z21object_alloc_byte_txvh): store i8 to *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(0x2a, deref($1)))",
            "./tests/cpp/tagged_union_vuln.cpp:38:3(@_Z21object_alloc_byte_tcvh): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x3, deref($0)))",
            "./tests/cpp/tagged_union_vuln.cpp:48:12(@_Z20object_alloc_byte_vth): store i32 to *<?_>!object-tag.cast-target@0+8: failed to verify cast as i32 under context and(eq(0x28757b2, deref($1)))",
            "./tests/cpp/tagged_union_vuln.cpp:49:3(@_Z20object_alloc_byte_vth): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as i32 under context and(eq(0x3, deref($0)), eq(0x28757b2, deref($1)))",
            "./tests/cpp/tagged_union_vuln.cpp:56:12(@_Z21object_alloc_byte_vcthPFvP6ObjectE): store i8 to *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(0x2a, deref($1)))",
            "./tests/cpp/tagged_union_vuln.cpp:58:3(@_Z21object_alloc_byte_vcthPFvP6ObjectE): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x3, deref($0)))",
            "./tests/cpp/tagged_union_vuln.cpp:82:11(@_Z13object_copy_tP6ObjectS0_): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(deref($1), deref($0)))",
            "./tests/cpp/tagged_union_vuln.cpp:87:11(@_Z13object_copy_vP6ObjectS0_): memcpy *<?_>!object-tag.cast-target@0+8 to *<?_>!object-tag.cast-target@0+8 with length 8: failed to verify cast equality under context and(eq(deref($2), deref($3)))",
            "./tests/cpp/tagged_union_vuln.cpp:93:3(@_Z15object_copy_vxtP6ObjectS0_): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x3, deref($0)), eq(deref($1), deref($2)))",
            "./tests/cpp/tagged_union_vuln.cpp:99:11(@_Z16object_copy_vxxtP6ObjectS0_): memcpy *<?_>!object-tag.cast-target@0+8 to *<?_>!object-tag.cast-target@0+8 with length 8: failed to verify cast equality under context and(eq(deref($2), deref($3)))",
            "./tests/cpp/tagged_union_vuln.cpp:102:11(@_Z16object_copy_vxxtP6ObjectS0_): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(deref($1), deref($0)), eq(0x2a, deref($2)))",
            "./tests/cpp/tagged_union_vuln.cpp:108:19(@_Z15object_neg_boolP6Object): load i8 from *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(deref($0), 0x2))",
            "./tests/cpp/tagged_union_vuln.cpp:116:5(@_Z15object_set_byteP6Objecth): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x4, deref($0)))",
            "./tests/cpp/tagged_union_vuln.cpp:117:14(@_Z15object_set_byteP6Objecth): store i8 to *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(0x4, deref($0)))",
            "./tests/cpp/tagged_union_vuln.cpp:124:20(@_Z15object_add_byteP6ObjectS0_): load i8 from *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(deref($0), 0x4))",
            "./tests/cpp/tagged_union_vuln.cpp:124:32(@_Z15object_add_byteP6ObjectS0_): load i8 from *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(deref($1), 0x4))",
            "./tests/cpp/tagged_union_vuln.cpp:132:27(@_Z25object_select_second_byteP6Objectm): load i8 from *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(deref($1), 0x3))",
            "./tests/cpp/tagged_union_vuln.cpp:149:17(@_Z17object_to_cstringP6Object): load %struct.String* from *<?_>!object-tag.cast-target@0+8: failed to verify cast as %struct.String* under context and()",
            "./tests/cpp/tagged_union_vuln.cpp:154:14(@_Z13keyvalue_copyP8KeyValueS0_): memcpy *<?_>!object-tag.cast-target@0+8 to *<?_>!object-tag.cast-target@0+8 with length 8: failed to verify cast equality under context and(eq(deref($2), deref($3)))",
            "./tests/cpp/tagged_union_vuln.cpp:155:16(@_Z13keyvalue_copyP8KeyValueS0_): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast equality under context and(eq(deref($2), deref($0)), eq(deref($3), deref($4)))",
        ],
        &vec![
            "./tests/cpp/tagged_union_vuln.cpp:67:3(@_Z21object_alloc_byte_vtdh): @_ZdlPv invalidates the given pointer",
            "./tests/cpp/tagged_union_vuln.cpp:76:3(@_Z21object_alloc_byte_vtfh): @free invalidates the given pointer",
            // NOTICE: alloca does not have debug information.
            "??(@_Z24use_object_alloca_uninitv): *<?_>%struct.Object is allocated with alloca as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:6:17(@_Z19object_alloc_byte_tv): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:7:3(@_Z19object_alloc_byte_tv): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:13:17(@_Z19object_alloc_byte_vh): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:14:12(@_Z19object_alloc_byte_vh): memcpy *<?_>i8 to *<?_>!object-tag.cast-target@0+8(%union.anon) with length 1",
            "./tests/cpp/tagged_union_vuln.cpp:20:17(@_Z20object_alloc_byte_tvh): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:21:3(@_Z20object_alloc_byte_tvh): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:22:12(@_Z20object_alloc_byte_tvh): memcpy *<?_>i8 to *<?_>!object-tag.cast-target@0+8(%union.anon) with length 1",
            "./tests/cpp/tagged_union_vuln.cpp:28:17(@_Z21object_alloc_byte_txvh): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:29:3(@_Z21object_alloc_byte_txvh): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:30:9(@_Z21object_alloc_byte_txvh): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:31:12(@_Z21object_alloc_byte_txvh): memcpy *<?_>i8 to *<?_>!object-tag.cast-target@0+8(%union.anon) with length 1",
            "./tests/cpp/tagged_union_vuln.cpp:37:17(@_Z21object_alloc_byte_tcvh): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:38:3(@_Z21object_alloc_byte_tcvh): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:47:17(@_Z20object_alloc_byte_vth): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:48:12(@_Z20object_alloc_byte_vth): memcpy *<?_>i32 to *<?_>!object-tag.cast-target@0+8(%union.anon) with length 4",
            "./tests/cpp/tagged_union_vuln.cpp:49:3(@_Z20object_alloc_byte_vth): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:55:17(@_Z21object_alloc_byte_vcthPFvP6ObjectE): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:56:12(@_Z21object_alloc_byte_vcthPFvP6ObjectE): memcpy *<?_>i8 to *<?_>!object-tag.cast-target@0+8(%union.anon) with length 1",
            "./tests/cpp/tagged_union_vuln.cpp:57:3(@_Z21object_alloc_byte_vcthPFvP6ObjectE): indirectly call *<?_>void (*<?_>%struct.Object)",
            "./tests/cpp/tagged_union_vuln.cpp:58:3(@_Z21object_alloc_byte_vcthPFvP6ObjectE): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:64:17(@_Z21object_alloc_byte_vtdh): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:73:17(@_Z21object_alloc_byte_vtfh): *<?_>%struct.Object is allocated with dynamic@malloc as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:82:11(@_Z13object_copy_tP6ObjectS0_): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:87:11(@_Z13object_copy_vP6ObjectS0_): memcpy *<?_>!object-tag.cast-target@0+8(%union.anon) to *<?_>!object-tag.cast-target@0+8(%union.anon) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:93:3(@_Z15object_copy_vxtP6ObjectS0_): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:99:11(@_Z16object_copy_vxxtP6ObjectS0_): memcpy *<?_>!object-tag.cast-target@0+8(%union.anon) to *<?_>!object-tag.cast-target@0+8(%union.anon) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:102:11(@_Z16object_copy_vxxtP6ObjectS0_): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:108:19(@_Z15object_neg_boolP6Object): load i8 from *<?_>!object-tag.cast-target@0+8(%union.anon)",
            "./tests/cpp/tagged_union_vuln.cpp:116:5(@_Z15object_set_byteP6Objecth): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:117:14(@_Z15object_set_byteP6Objecth): memcpy *<?_>i8 to *<?_>!object-tag.cast-target@0+8(%union.anon) with length 1",
            "./tests/cpp/tagged_union_vuln.cpp:124:20(@_Z15object_add_byteP6ObjectS0_): load i8 from *<?_>!object-tag.cast-target@0+8(%union.anon)",
            "./tests/cpp/tagged_union_vuln.cpp:124:32(@_Z15object_add_byteP6ObjectS0_): load i8 from *<?_>!object-tag.cast-target@0+8(%union.anon)",
            "./tests/cpp/tagged_union_vuln.cpp:132:20(@_Z25object_select_second_byteP6Objectm): non-zero index 16 from *<?_>%struct.Object",
            "./tests/cpp/tagged_union_vuln.cpp:132:27(@_Z25object_select_second_byteP6Objectm): load i8 from *<?_>!object-tag.cast-target@0+8(%union.anon)",
            "./tests/cpp/tagged_union_vuln.cpp:139:13(@_Z20object_overwrite_tagP6Object): memcpy *<?_>*<?_>!object-tag.cast-tag0@0+0(i64) to *<?_>*<?_>i64 with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:149:17(@_Z17object_to_cstringP6Object): load *<?_>%struct.String from *<?_>!object-tag.cast-target@0+8(%union.anon)",
            "./tests/cpp/tagged_union_vuln.cpp:154:14(@_Z13keyvalue_copyP8KeyValueS0_): memcpy *<?_>!object-tag.cast-target@0+8(%union.anon) to *<?_>!object-tag.cast-target@0+8(%union.anon) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:155:16(@_Z13keyvalue_copyP8KeyValueS0_): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_vuln.cpp:166:17(@_Z24use_object_malloc_uninitv): *<?_>%struct.Object is allocated with dynamic@malloc as containing extension types",
            "./tests/cpp/tagged_union_vuln.cpp:172:17(@_Z21use_object_new_uninitv): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
        ],
    );
}

#[test]
fn test_tagged_union_restrict() {
    assert_typechk(
        "tagged_union_restrict.ll",
        Some("tagged_union.lisp"),
        &vec![],
        &vec![
            "./tests/cpp/tagged_union_restrict.cpp:5:24(@_Z20alloc_context_inlineP7Closure): *<?_>%struct.ContextInline is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_restrict.cpp:6:11(@_Z20alloc_context_inlineP7Closure): escape !object-tag.cast-target@0+8(%union.anon) from *<?_>!object-closure-tag.restrict-base@1+0(%struct.Object) at offset 8 via getelementptr",
            "./tests/cpp/tagged_union_restrict.cpp:7:3(@_Z20alloc_context_inlineP7Closure): escape !object-tag.cast-tag0@0+0(i64) from *<?_>!object-closure-tag.restrict-base@1+0(%struct.Object) at offset 0 via getelementptr",
            "./tests/cpp/tagged_union_restrict.cpp:8:15(@_Z20alloc_context_inlineP7Closure): escape !object-tag.cast-target@0+8(%union.anon) from *<?_>!object-byte-tag.restrict-base@2+16(%struct.Object) at offset 8 via getelementptr",
            "./tests/cpp/tagged_union_restrict.cpp:9:3(@_Z20alloc_context_inlineP7Closure): escape !object-tag.cast-tag0@0+0(i64) from *<?_>!object-byte-tag.restrict-base@2+16(%struct.Object) at offset 0 via getelementptr",
            "./tests/cpp/tagged_union_restrict.cpp:15:17(@_Z27context_inline_call_closureP13ContextInlinePv): escape !object-tag.cast-target@0+8(%union.anon) from *<?_>!object-closure-tag.restrict-base@1+0(%struct.Object) at offset 8 via getelementptr",
            "./tests/cpp/tagged_union_restrict.cpp:16:15(@_Z27context_inline_call_closureP13ContextInlinePv): escape !object-tag.cast-target@0+8(%union.anon) from *<?_>!object-byte-tag.restrict-base@2+16(%struct.Object) at offset 8 via getelementptr",
            "./tests/cpp/tagged_union_restrict.cpp:17:10(@_Z27context_inline_call_closureP13ContextInlinePv): indirectly call *<?_>i32 (*<?_>i8, *<?_>i8)",
        ],
    );
}

#[test]
fn test_tagged_union_restrict_vuln() {
    assert_typechk(
        "tagged_union_restrict_vuln.ll",
        Some("tagged_union.lisp"),
        &vec![
            "./tests/cpp/tagged_union_restrict_vuln.cpp:7:3(@_Z20alloc_context_inlineP7Closure): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as %struct.Closure* under context and(eq(0x3, deref($0)))",
            "./tests/cpp/tagged_union_restrict_vuln.cpp:9:3(@_Z20alloc_context_inlineP7Closure): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as i8 under context and(eq(0x8, deref($0)), eq(0x0, deref($1)))",
        ],
        &vec![
            "./tests/cpp/tagged_union_restrict_vuln.cpp:5:24(@_Z20alloc_context_inlineP7Closure): *<?_>%struct.ContextInline is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_restrict_vuln.cpp:6:11(@_Z20alloc_context_inlineP7Closure): escape !object-tag.cast-target@0+8(%union.anon) from *<?_>!object-closure-tag.restrict-base@1+0(%struct.Object) at offset 8 via getelementptr",
            "./tests/cpp/tagged_union_restrict_vuln.cpp:7:3(@_Z20alloc_context_inlineP7Closure): escape !object-tag.cast-tag0@0+0(i64) from *<?_>!object-closure-tag.restrict-base@1+0(%struct.Object) at offset 0 via getelementptr",
            "./tests/cpp/tagged_union_restrict_vuln.cpp:7:3(@_Z20alloc_context_inlineP7Closure): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_restrict_vuln.cpp:8:15(@_Z20alloc_context_inlineP7Closure): escape !object-tag.cast-target@0+8(%union.anon) from *<?_>!object-byte-tag.restrict-base@2+16(%struct.Object) at offset 8 via getelementptr",
            "./tests/cpp/tagged_union_restrict_vuln.cpp:9:3(@_Z20alloc_context_inlineP7Closure): escape !object-tag.cast-tag0@0+0(i64) from *<?_>!object-byte-tag.restrict-base@2+16(%struct.Object) at offset 0 via getelementptr",
            "./tests/cpp/tagged_union_restrict_vuln.cpp:9:3(@_Z20alloc_context_inlineP7Closure): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
        ],
    );
}

#[test]
fn test_tagged_union_unsupported() {
    assert_typechk(
        "tagged_union_unsupported.ll",
        Some("tagged_union.lisp"),
        &vec![
            // Not so smart warning resolution across branches even under safe code.
            // In this case, it is easier to check the code is safe.
            // However, in general cases, loops make this resolution process very hard.
            "./tests/cpp/tagged_union_unsupported.cpp:6:3(@_Z21object_alloc_byte_tcvh): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x3, deref($0)))",
            // Unsupported because assigning to *pctx is treated as assignment of value with type uint32_t.
            // Type uint32_t is subtype of type of Object.h (uiont64_t), hence the assignment is considered as side-effect.
            "./tests/cpp/tagged_union_unsupported.cpp:24:23(@_Z23object_add_byte_withcntP6ObjectS0_S0_Pj): load i8 from *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and()",
            "./tests/cpp/tagged_union_unsupported.cpp:24:35(@_Z23object_add_byte_withcntP6ObjectS0_S0_Pj): load i8 from *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and()",
        ],
        &vec![
            "./tests/cpp/tagged_union_unsupported.cpp:5:17(@_Z21object_alloc_byte_tcvh): *<?_>%struct.Object is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/tagged_union_unsupported.cpp:6:3(@_Z21object_alloc_byte_tcvh): memcpy *<?_>i64 to *<?_>!object-tag.cast-tag0@0+0(i64) with length 8",
            "./tests/cpp/tagged_union_unsupported.cpp:24:23(@_Z23object_add_byte_withcntP6ObjectS0_S0_Pj): load i8 from *<?_>!object-tag.cast-target@0+8(%union.anon)",
            "./tests/cpp/tagged_union_unsupported.cpp:24:35(@_Z23object_add_byte_withcntP6ObjectS0_S0_Pj): load i8 from *<?_>!object-tag.cast-target@0+8(%union.anon)",
        ],
    );
}

#[test]
fn test_single_inherit_class() {
    assert_typechk(
        "single_inherit_class.ll",
        Some("single_inherit_class.lisp"),
        &vec![],
        &vec![
            "??(@_Z32use_single_inherit_class2_allocai): *<?_>%struct.SingleInheritClass2 is allocated with alloca as containing extension types",
            "./tests/cpp/single_inherit_class.cpp:5:31(@_Z27alloc_single_inherit_class1h): *<?_>%struct.SingleInheritClass1 is allocated with dynamic@_Znwm as containing extension types",
            // FIXME: This out-of-bound access warning can be resolved by the subsequent safe downcast.
            // Currently, this is not resolved because this warning is not one of CastReason.
            "./tests/cpp/single_inherit_class.cpp:14:43(@_Z25single_inherit_class2_incP18SingleInheritClass): escape i32 from *<?_>%struct.SingleInheritClass at offset 8 via getelementptr",
        ],
    );
}

#[test]
fn test_single_inherit_class_vuln() {
    assert_typechk(
        "single_inherit_class_vuln.ll",
        Some("single_inherit_class.lisp"),
        &vec![
            "./tests/cpp/single_inherit_class_vuln.cpp:6:11(@_Z26alloc_single_inherit_classv): store i64 to *<?_>!single-inherit-class-tag.downcast-tag0@0+0: failed to verify cast as %struct.SingleInheritClass under context and()",
            "./tests/cpp/single_inherit_class_vuln.cpp:13:11(@_Z27alloc_single_inherit_class1h): store i64 to *<?_>!single-inherit-class-tag.downcast-tag0@0+0: failed to verify cast as %struct.SingleInheritClass under context and()",
            "./tests/cpp/single_inherit_class_vuln.cpp:14:24(@_Z27alloc_single_inherit_class1h): downcast *<?_>!single-inherit-class-tag.downcast-target@0+0 with target %struct.SingleInheritClass1: failed to verify cast as %struct.SingleInheritClass1 under context and()",
            "./tests/cpp/single_inherit_class_vuln.cpp:22:14(@_Z27alloc_single_inherit_class2v): store i64 to *<?_>!single-inherit-class-tag.downcast-tag0@0+0: failed to verify cast as %struct.SingleInheritClass2 under context and(eq(0x1, deref($0)))",
            // Casting between SingleInheritClass1* and SingleInheritClass2* is not checked, because neither is refiner target.
            "./tests/cpp/single_inherit_class_vuln.cpp:31:11(@_Z32single_inherit_class_transform12P19SingleInheritClass1): store i64 to *<?_>!single-inherit-class-tag.downcast-tag0@0+0: failed to verify cast as %struct.SingleInheritClass under context and()",
            "./tests/cpp/single_inherit_class_vuln.cpp:32:24(@_Z32single_inherit_class_transform12P19SingleInheritClass1): downcast *<?_>!single-inherit-class-tag.downcast-target@0+0 with target %struct.SingleInheritClass2: failed to verify cast as %struct.SingleInheritClass2 under context and()",
            "./tests/cpp/single_inherit_class_vuln.cpp:39:41(@_Z25single_inherit_class2_incP18SingleInheritClass): downcast *<?_>!single-inherit-class-tag.downcast-target@0+0 with target %struct.SingleInheritClass2: failed to verify cast as %struct.SingleInheritClass2 under context and()",
        ],
        &vec![
            "??(@_Z32use_single_inherit_class1_allocah): *<?_>%struct.SingleInheritClass1 is allocated with alloca as containing extension types",
            "./tests/cpp/single_inherit_class_vuln.cpp:5:29(@_Z26alloc_single_inherit_classv): *<?_>%struct.SingleInheritClass is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/single_inherit_class_vuln.cpp:6:11(@_Z26alloc_single_inherit_classv): memcpy *<?_>i64 to *<?_>!single-inherit-class-tag.downcast-tag0@0+0(i64) with length 8",
            "./tests/cpp/single_inherit_class_vuln.cpp:12:29(@_Z27alloc_single_inherit_class1h): *<?_>%struct.SingleInheritClass is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/single_inherit_class_vuln.cpp:13:11(@_Z27alloc_single_inherit_class1h): memcpy *<?_>i64 to *<?_>!single-inherit-class-tag.downcast-tag0@0+0(i64) with length 8",
            "./tests/cpp/single_inherit_class_vuln.cpp:14:24(@_Z27alloc_single_inherit_class1h): *<?_>%struct.SingleInheritClass is cast as *<?_>%struct.SingleInheritClass1",
            "./tests/cpp/single_inherit_class_vuln.cpp:21:31(@_Z27alloc_single_inherit_class2v): *<?_>%struct.SingleInheritClass2 is allocated with dynamic@_Znwm as containing extension types",
            "./tests/cpp/single_inherit_class_vuln.cpp:22:14(@_Z27alloc_single_inherit_class2v): memcpy *<?_>i64 to *<?_>!single-inherit-class-tag.downcast-tag0@0+0(i64) with length 8",
            "./tests/cpp/single_inherit_class_vuln.cpp:23:35(@_Z27alloc_single_inherit_class2v): *<?_>%struct.SingleInheritClass2 is cast as *<?_>%struct.SingleInheritClass1",
            "./tests/cpp/single_inherit_class_vuln.cpp:31:11(@_Z32single_inherit_class_transform12P19SingleInheritClass1): memcpy *<?_>i64 to *<?_>!single-inherit-class-tag.downcast-tag0@0+0(i64) with length 8",
            "./tests/cpp/single_inherit_class_vuln.cpp:32:24(@_Z32single_inherit_class_transform12P19SingleInheritClass1): *<?_>%struct.SingleInheritClass is cast as *<?_>%struct.SingleInheritClass2",
            "./tests/cpp/single_inherit_class_vuln.cpp:39:41(@_Z25single_inherit_class2_incP18SingleInheritClass): *<?_>%struct.SingleInheritClass is cast as *<?_>%struct.SingleInheritClass2",
            "./tests/cpp/single_inherit_class_vuln.cpp:39:41(@_Z25single_inherit_class2_incP18SingleInheritClass): escape i32 from *<?_>%struct.SingleInheritClass at offset 8 via getelementptr",
            // use_single_inherit_class1_alloca is vulnerable because calling single_inherit_class2_inc as passing SingleInheritClass1 by reference.
            // However, this call is not vulnerable because SingleInheritClass1 is subtype of SingleInheritClass.
            // The internal behaviour in single_inherit_class2_inc may be vulnerable under some unexpected arguments, this is already warned.
        ],
    );
}

#[test]
fn test_single_inherit_class_vuln_annot() {
    assert_eq!(
        typechk("single_inherit_class.ll", Some("single_inherit_class_vuln.lisp")),
        Err(String::from("conflict case and(eq(bitand(deref($0), 0xff), 0x1)) -> %struct.SingleInheritClass1 and case and(eq(bitand(deref($0), 0xff), 0x1)) -> %struct.SingleInheritClass2 between incompatible types")),
    );
}
