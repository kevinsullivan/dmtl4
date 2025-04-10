def describe (x : Int) : String :=
  if x < 0 then "Neg"
  else if x == 0 then "Zero"
  else "Pos"
