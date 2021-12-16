(define-refiner object-tag (cast-match
    ((== (bitand (deref $0) 0xff) 0x00) void)
    ((== (bitand (deref $0) 0xff) 0x01) void)
    ((== (bitand (deref $0) 0xff) 0x02) void)
    ((== (bitand (deref $0) 0xff) 0x03) i8)
    ((== (bitand (deref $0) 0xff) 0x04) i32)
    ((== (bitand (deref $0) 0xff) 0x08) (ptr "struct.Closure"))))
  
(apply-refiner "struct.Object" (fieldptr 1) (cast object-tag (fieldptr 0)))

(define-refiner object-closure-tag (restrict-cast-match object-tag (ptr "struct.Closure")))
(apply-refiner "struct.ContextInline" (fieldptr 0) (restrict object-closure-tag))
(define-refiner object-byte-tag (restrict-cast-match object-tag i8))
(apply-refiner "struct.ContextInline" (fieldptr 1) (restrict object-byte-tag))
