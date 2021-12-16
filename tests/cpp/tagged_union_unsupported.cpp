#include "./tagged_union.hpp"

Object *object_alloc_byte_tcv(uint8_t x)
{
  Object *obj = new Object;
  object_set_tag(obj, OBJECT_ID_BYTE);
  if (x != 0) {
    obj->v.b = x;
  } else {
    obj->v.b = 0;
  }
  return obj;
}

void object_add_byte_withcnt(Object *obj1, Object *obj2, Object *obj3, uint32_t *pctx)
{
  if (!object_is_byte(obj1)) {
    return;
  }
  if (!object_is_byte(obj2)) {
    return;
  }
  *pctx += 1;
  obj3->v.b = obj1->v.b + obj2->v.b;
  object_set_tag(obj3, OBJECT_ID_BYTE);
}
