{
  def fac(n:Int):Int = n match
  {
  case 0 => 1
  case n => n * fac (n - 1)
  };
  fac(3)
}
