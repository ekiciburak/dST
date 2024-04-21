  process : Type
  participant : Type
  label : Type
  sort : Type
  list : Functor
  prod: Functor

  psend     : process
  pssend    : participant -> label -> sort -> process -> process
  psreceive : participant -> "list" ("prod" ("prod" (label, sort), process)) -> process
  psite     : sort -> process -> process -> process
  psmu      : (process -> process) -> process