#include "./tagged_union.hpp"

ContextInline *alloc_context_inline(Closure *cl)
{
  ContextInline *ctx = new ContextInline;
  ctx->cl.v.cl = cl;
  object_set_tag(&ctx->cl, OBJECT_ID_CLOSURE);
  ctx->ncalls.v.b = 0;
  object_set_tag(&ctx->ncalls, OBJECT_ID_BYTE);
  return ctx;
}

int context_inline_call_closure(ContextInline *ctx, void *arg)
{
  Closure *cl = object_get_closure(&ctx->cl);
  ctx->ncalls.v.b += 1;
  return cl->fnptr(cl->env, arg);
}
