  Z: Type
  bool: Type
  sort: Type

  sint   : sort
  sbool  : sort 
  sci    : Z -> sort
  scb    : bool -> sort
  spi    : (sort -> sort) -> sort -> sort -> sort
  slambda: (sort -> sort) -> sort -> sort -> sort
  ssig   : (sort -> sort) -> sort -> sort -> sort
  splus  : sort -> sort -> sort
  sminus : sort -> sort -> sort
  sgt    : sort -> sort -> sort
  seq    : sort -> sort -> sort
  sapp   : sort -> sort -> sort
  sstar  : sort
  site   : sort -> sort -> sort -> sort 
  spair  : (sort -> sort) -> sort -> sort -> sort
  sextst : sort -> sort -> sort
  sneg   : sort -> sort
  sand   : sort -> sort -> sort
  sor    : sort -> sort -> sort