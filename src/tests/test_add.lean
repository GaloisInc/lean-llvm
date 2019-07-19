
def add (x y : Nat) : Nat := x + y

def cont {A} (x:A) (f: A → A → A) := λy => f y x
