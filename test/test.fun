|
                 def foo(s : List[Int]) : Int = s match
                  {
                  case List(_, u) => u + 2
                  };
                  1000 * foo(List(2, 4)) + foo(List(3, 4, 5))
                }