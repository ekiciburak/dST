  local : Type
  participant : Type
  label : Type
  list : Functor
  prod: Functor

  ltend     : local
  ltsend    : participant -> label -> local -> local -> local
  ltreceive : participant -> "list" ("prod" ("prod" (label, local), local)) -> local
  ltselect  : participant -> "list" ("prod" ("prod" (label, local), local)) -> local
  ltbranch  : participant -> "list" ("prod" ("prod" (label, local), local)) -> local
  ltmu      : (local -> local) -> local -> local
  ltpi      : (local -> local) -> local -> local
  ltlambda  : (local -> local) -> local -> local
  ltsig     : (local -> local) -> local -> local
  ltite     : local -> local -> local -> local
  ltpair    : local -> local -> local
  ltzero    : local
  ltsucc    : local -> local
  ltfalse   : local
  lttrue    : local
  ltnat     : local
  ltbool    : local
  ltstar    : local

