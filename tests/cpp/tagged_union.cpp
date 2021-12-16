#include "./tagged_union.hpp"
#include <cstddef>

Object *object_alloc_bool_vt(int b)
{
  Object *obj = new Object;
  if (b) {
    object_set_tag(obj, OBJECT_ID_TRUE);
  } else {
    object_set_tag(obj, OBJECT_ID_FALSE);
  }
  return obj;
}

Object *object_alloc_byte_tv(uint8_t x)
{
  Object *obj = new Object;
  object_set_tag(obj, OBJECT_ID_BYTE);
  obj->v.b = x;
  return obj;
}

Object *object_alloc_byte_vt(uint8_t x)
{
  Object *obj = new Object;
  obj->v.b = x;
  object_set_tag(obj, OBJECT_ID_BYTE);
  return obj;
}

Object *object_alloc_closure(Closure *cl)
{
  Object *obj = new Object;
  obj->v.cl = cl;
  object_set_tag(obj, OBJECT_ID_CLOSURE);
  return obj;
}

void object_copy_vt(Object *obj1, Object *obj2)
{
  obj1->v = obj2->v;
  obj1->h = obj2->h;
}

void object_copy_tv(Object *obj1, Object *obj2)
{
  obj1->h = obj2->h;
  obj1->v = obj2->v;
}

int object_neg_bool(Object *obj)
{
  if (object_is_true(obj)) {
    return 0;
  }
  return 1;
}

void object_set_byte(Object *obj, uint8_t x)
{
  if (object_is_byte(obj)) {
    obj->v.b = x;
  }
}

void object_set_add_byte(Object *obj, uint8_t x)
{
  if (object_is_byte(obj)) {
    obj->v.b = obj->v.b + x;
  }
}

int object_add_byte(Object *obj1, Object *obj2)
{
  if (object_is_byte(obj1) && object_is_byte(obj2)) {
    return obj1->v.b + obj2->v.b;
  }
  return -1;
}

int object_select_second_byte(Object *objbase, size_t nobjs)
{
  if (nobjs >= 2 && object_is_byte(objbase+1)) {
    return (objbase+1)->v.b;
  }
  return -1;
}

void keyvalue_copy(KeyValue *kv1, KeyValue *kv2)
{
  kv1->key.v = kv2->key.v;
  kv1->key.h = kv2->key.h;
  kv1->value.v = kv2->value.v;
  kv1->value.h = kv2->value.h;
}

void use_object_alloca(void)
{
  Object obj;
  obj.v.b = 42;
  object_set_tag(&obj, OBJECT_ID_BYTE);
  object_inc_byte(&obj);
}
