  participant: Type
  sort       : Type
  local      : Type
  label      : Type
  type       : Type
  list       : Functor
  prod       : Functor

  ltsel    : participant -> "list" ("prod" (label, local)) -> local
  ltbrn    : participant -> "list" ("prod" (label, local)) -> local  
  ltreceive: participant -> type -> local -> local
  ltsend   : participant -> type -> local -> local
  ltmu     : sort -> (local -> local) -> local
  ltend    : local