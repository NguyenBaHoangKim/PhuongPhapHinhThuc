sig A {}   -- a
sig B {}   -- b
sig C {}   -- c
sig D {}   -- d

-- a      → some A
--¬a     → no A
--a ∧ b  → some A and some B
--a ∨ b  → some A or some B
--a ⇒ b  → some A implies some B
--a = b  → some A iff some B
--a ≠ b (xor)    → (a and ¬b) or (¬a and b)/ some A iff no B


-- (1) a ∧ ¬b ⇒ a∨b
assert f1 {
    (some A and no B) implies (some A or some B)
}
check f1 for 1

-- (2) (a⇒b)⇒a = a
assert f2 {
    ((some A implies some B) implies some A) iff some A
}
check f2 for 1

-- (3) a ∧ ¬a ⇒ b
assert f3 {
    (some A and no A) implies some B
}
check f3 for 1

-- (4) (a⇒b) ∨ (b⇒a)
assert f4 {
    (some A implies some B) or (some B implies some A)
}
check f4 for 1

-- (5) ¬(a ∧ ¬(a∨b))
assert f5 {
    not (some A and not (some A or some B))
}
check f5 for 1

-- (6) a=b ∨ a=c ∨ b=c
assert f6 {
    (some A iff some B) or (some A iff some C) or (some B iff some C)
}
check f6 for 1

-- (7) (a ⇒ ¬a) ⇒ ¬a
assert f7 {
    (some A implies no A) implies no A
}
check f7 for 1

-- (8) (a⇒b) ∧ (¬a ⇒ b) = b
assert f8 {
    ((some A implies some B) and (no A implies some B)) iff some B
}
check f8 for 1

-- (9) a⇒(b⇒a)
assert f9 {
    some A implies (some B implies some A)
}
check f9 for 1

-- (11) a∧b ∨ a∧¬b == a
assert f11 {
    ((some A and some B) or (some A and no B)) iff some A
}
check f11 for 1

-- (12) a ⇒ a∧b == a⇒b == a∨b ⇒ b
assert f12 {
    (some A implies (some A and some B))
        iff (some A implies some B)
        iff ((some A or some B) implies some B)
}
check f12 for 1

-- (13) (¬a⇒¬b) ∧ (a⧧b) ∨ (a∧c ⇒ b∧c)
assert f13 {
    (
        ((no A) implies (no B))
        and
        ((some A and no B) or (no A and some B))  -- XOR
    )
    or
    (
        (some A and some C) implies (some B and some C)
    )
}
check f13 for 1

-- (14) (a ⇒ a∧b) ∨ (b ⇒ a∧b)
assert f14 {
    (some A implies (some A and some B))
    or
    (some B implies (some A and some B))
}
check f14 for 1

-- (15) (a⇒b) ∧ (c⇒d) ∧ (a∨c) ⇒ (b∨d)
assert f15 {
    (
        (some A implies some B)
        and
        (some C implies some D)
        and
        (some A or some C)
    )
    implies
    (some B or some D)
}
check f15 for 1

-- (16) (a⇒b⇒¬a) ∨ (b∧c ⇒ a∧c)
assert f16 {
    (some A implies (some B implies no A))
    or
    ((some B and some C) implies (some A and some C))
}
check f16 for 1
