#include "single_inherit_class.hpp"

SingleInheritClass1 *alloc_single_inherit_class1(uint8_t b)
{
  SingleInheritClass1 *cls1 = new SingleInheritClass1;
  cls1->h.id = SINGLE_INHERIT_CLASS_ID_1;
  cls1->b = b;
  return cls1;
}

int single_inherit_class2_inc(SingleInheritClass *cls)
{
  if (cls->id == SINGLE_INHERIT_CLASS_ID_2) {
    return ((SingleInheritClass2 *) cls)->i + 1;
  }
  return -1;
}

int use_single_inherit_class2_alloca(int32_t i)
{
  SingleInheritClass2 cls2;
  cls2.h.id = SINGLE_INHERIT_CLASS_ID_2;
  cls2.i = i;
  return single_inherit_class2_inc((SingleInheritClass *) &cls2);
}
