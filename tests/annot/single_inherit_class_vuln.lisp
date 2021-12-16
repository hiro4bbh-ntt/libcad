(define-refiner single-inherit-class-tag (cast-match
    ((== (bitand (deref $0) 0xff) 0x01) "struct.SingleInheritClass1")
    ((== (bitand (deref $0) 0xff) 0x01) "struct.SingleInheritClass2")))
  
(apply-refiner "struct.SingleInheritClass" baseptr (downcast single-inherit-class-tag (fieldptr 0)))
