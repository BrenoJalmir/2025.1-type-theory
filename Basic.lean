def curry (f : α × β → γ) (x : α) (y : β) : γ :=
f (x, y)

def uncurry (f : α → β → γ) : α × β → γ := λ(x, y) =>
f x y

-- def joinStringsWith : String → String → String → String :=
def joinStringsWith (s₁ s₂ s₃ : String) : String :=
String.append (String.append s₂ s₁) s₃

#eval joinStringsWith ", " "one" "and another"
#check joinStringsWith ": "

-- def volume (height width depth : Nat) : Nat :=
-- height * width * depth

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := {x := 0.0, y := 0.0}

#eval origin

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr

-- #eval {height := 5, width := 5, depth := 5 : RectangularPrism}
def volume (rp : RectangularPrism) : Float :=
rp.height * rp.width * rp.depth

structure Segment where
  p₁ : Point
  p₂ : Point
deriving Repr

def length (seg : Segment) : Float :=
Float.sqrt (((seg.p₂.x - seg.p₁.x) ^ 2.0) + ((seg.p₂.y - seg.p₁.y) ^ 2.0))

def fiveOverX : Point := {x := 5, y := 5}

#eval length {p₁ := origin, p₂ := fiveOverX}
