#include "./single_inherit_class.hpp"

SingleInheritClass *alloc_single_inherit_class(void)
{
  SingleInheritClass *cls = new SingleInheritClass;
  cls->id = SINGLE_INHERIT_CLASS_ID_1;
  return cls;
}

SingleInheritClass1 *alloc_single_inherit_class1(uint8_t b)
{
  SingleInheritClass *cls = new SingleInheritClass;
  cls->id = SINGLE_INHERIT_CLASS_ID_1;
  SingleInheritClass1 *cls1 = (SingleInheritClass1 *) cls;
  cls1->b = b;
  return cls1;
}

SingleInheritClass2 *alloc_single_inherit_class2(void)
{
  SingleInheritClass2 *cls2 = new SingleInheritClass2;
  cls2->h.id = SINGLE_INHERIT_CLASS_ID_1;
  ((SingleInheritClass1 *) cls2)->b = 0;
  return cls2;
}

SingleInheritClass2 *single_inherit_class_transform12(SingleInheritClass1 *cls1)
{
  uint8_t b = cls1->b;
  SingleInheritClass *cls = (SingleInheritClass *) cls1;
  cls->id = SINGLE_INHERIT_CLASS_ID_2;
  SingleInheritClass2 *cls2 = (SingleInheritClass2 *) cls;
  cls2->i = b;
  return cls2;
}

int single_inherit_class2_inc(SingleInheritClass *cls)
{
  return ((SingleInheritClass2 *) cls)->i + 1;
}

int use_single_inherit_class1_alloca(uint8_t b)
{
  SingleInheritClass1 cls1;
  cls1.h.id = SINGLE_INHERIT_CLASS_ID_1;
  cls1.b = b;
  return single_inherit_class2_inc((SingleInheritClass *) &cls1);
}
