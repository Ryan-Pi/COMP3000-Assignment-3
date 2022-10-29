{
  val fac : Int => Int = (n : Int) => if(n < 2) 1 else n * fac (n - 1);
  fac(3)
}
