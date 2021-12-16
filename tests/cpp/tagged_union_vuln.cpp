#include "./tagged_union.hpp"
#include <cstdlib>

Object *object_alloc_byte_t(void)
{
  Object *obj = new Object;
  object_set_tag(obj, OBJECT_ID_BYTE);
  return obj;
}

Object *object_alloc_byte_v(uint8_t x)
{
  Object *obj = new Object;
  obj->v.b = 42;
  return obj;
}

Object *object_alloc_byte_tv(uint8_t x)
{
  Object *obj = new Object;
  object_set_tag(obj, OBJECT_ID_CLOSURE);
  obj->v.b = 42;
  return obj;
}

Object *object_alloc_byte_txv(uint8_t x)
{
  Object *obj = new Object;
  object_set_tag(obj, OBJECT_ID_BYTE);
  obj = new Object;
  obj->v.b = 42;
  return obj;
}

Object *object_alloc_byte_tcv(uint8_t x)
{
  Object *obj = new Object;
  object_set_tag(obj, OBJECT_ID_BYTE);
  if (x != 0) {
    obj->v.b = x;
  }
  return obj;
}

Object *object_alloc_byte_vt(uint8_t x)
{
  Object *obj = new Object;
  obj->v.i = 42424242;
  object_set_tag(obj, OBJECT_ID_BYTE);
  return obj;
}

Object *object_alloc_byte_vct(uint8_t x, void (*cb)(Object *obj))
{
  Object *obj = new Object;
  obj->v.b = 42;
  (*cb)(obj);
  object_set_tag(obj, OBJECT_ID_BYTE);
  return obj;
}

Object *object_alloc_byte_vtd(uint8_t x)
{
  Object *obj = new Object;
  obj->v.b = 42;
  object_set_tag(obj, OBJECT_ID_BYTE);
  delete obj;
  return obj;
}

Object *object_alloc_byte_vtf(uint8_t x)
{
  Object *obj = (Object *) malloc(sizeof(Object));
  obj->v.b = 42;
  object_set_tag(obj, OBJECT_ID_BYTE);
  free(obj);
  return obj;
}

void object_copy_t(Object *obj1, Object *obj2)
{
  obj1->h = obj2->h;
}

void object_copy_v(Object *obj1, Object *obj2)
{
  obj1->v = obj2->v;
}

void object_copy_vxt(Object *obj1, Object *obj2)
{
  obj1->v = obj2->v;
  object_set_tag(obj2, OBJECT_ID_BYTE);
  obj1->h = obj2->h;
}

void object_copy_vxxt(Object *obj1, Object *obj2)
{
  obj1->v = obj2->v;
  obj2->v.b = 42;
  object_set_tag(obj2, OBJECT_ID_BYTE);
  obj1->h = obj2->h;
}

int object_neg_bool(Object *obj)
{
  if (object_is_true(obj)) {
    return obj->v.b;
  }
  return 1;
}

void object_set_byte(Object *obj, uint8_t x)
{
  if (object_is_byte(obj)) {
    object_set_tag(obj, OBJECT_ID_INT);
    obj->v.b = x;
  }
}

int object_add_byte(Object *obj1, Object *obj2)
{
  if (object_is_int(obj1)) {
    return obj1->v.b + obj2->v.b;
  }
  return -1;
}

int object_select_second_byte(Object *objbase, size_t nobjs)
{
  if (nobjs >= 2 && object_is_byte(objbase+0)) {
    return (objbase+1)->v.b;
  }
  return -1;
}

void object_overwrite_tag(Object *obj)
{
  uint64_t *ph = &obj->h;
  *ph = OBJECT_ID_STRING;
}

uint8_t *object_to_cstring(Object *obj)
{
  // This test uses the following implicit fact:
  //   %struct.Object = type { i64, %union.anon }
  //   %union.anon = type { %struct.String }
  // This means that %union.anon seems to be %struct.String in LLIR.
  return obj->v.str->buf;
}

void keyvalue_copy(KeyValue *kv1, KeyValue *kv2)
{
  kv1->key.v = kv2->key.v;
  kv1->value.h = kv2->value.h;
}

int use_object_alloca_uninit(void)
{
  Object obj;
  return object_inc_byte(&obj);
}

int use_object_malloc_uninit(void)
{
  Object *obj = (Object *) malloc(sizeof(Object));
  return object_inc_byte(obj);
}

int use_object_new_uninit(void)
{
  Object *obj = new Object;
  return object_inc_byte(obj);
}
