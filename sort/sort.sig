  base: Type
  sort: Type

  sbase : base -> sort
  spi   : (sort -> sort) -> sort -> sort
  ssig  : (sort -> sort) -> sort -> sort
  splus : sort -> sort -> sort
  sneg  : sort -> sort -> sort
  sgt   : sort -> sort -> sort
  seq   : sort -> sort -> sort
  sapp  : sort -> sort -> sort

