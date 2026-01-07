module DiningPhilosophers_Tutorial
open util/ordering[HeThong] as Ord

sig TrietGia { niaTrai, niaPhai: one Nia }
sig Nia {}

fact BanTron {
  #TrietGia = 5
  #Nia = 5
  all p: TrietGia | p.niaTrai != p.niaPhai
  all n: Nia | one pL: TrietGia | pL.niaTrai = n
  all n: Nia | one pR: TrietGia | pR.niaPhai = n
}

abstract sig TrangThai {}
one sig SuyNghi, Doi, An extends TrangThai {}

sig HeThong {
  trangThai: TrietGia -> one TrangThai,
  hold: Nia -> lone TrietGia
}

fun cam[s: HeThong, p: TrietGia]: set Nia { (s.hold).p }

fact Invariants {
  all s: HeThong, p: TrietGia |
    (s.trangThai[p] = An) iff
      (p.niaTrai.(s.hold) = p and p.niaPhai.(s.hold) = p)

  all s: HeThong, p: TrietGia |
    s.trangThai[p] = SuyNghi implies no cam[s, p]
}

pred Init[s: HeThong] {
  all p: TrietGia | s.trangThai[p] = SuyNghi
  no s.hold
}

pred BecomeHungry[s, s2: HeThong, p: TrietGia] {
  s.trangThai[p] = SuyNghi
  s2.trangThai = s.trangThai ++ (p -> Doi)
  s2.hold = s.hold
}

pred StartEating[s, s2: HeThong, p: TrietGia] {
  s.trangThai[p] = Doi
  no p.niaTrai.(s.hold)
  no p.niaPhai.(s.hold)
  s2.hold = s.hold ++ (p.niaTrai -> p) ++ (p.niaPhai -> p)
  s2.trangThai = s.trangThai ++ (p -> An)
}

pred FinishEating[s, s2: HeThong, p: TrietGia] {
  s.trangThai[p] = An
  s2.hold = s.hold - (p.niaTrai -> TrietGia) - (p.niaPhai -> TrietGia)
  s2.trangThai = s.trangThai ++ (p -> SuyNghi)
}

pred Step[s, s2: HeThong] {
  some p: TrietGia |
    BecomeHungry[s, s2, p]
    or StartEating[s, s2, p]
    or FinishEating[s, s2, p]
}

fact Trace {
  Init[Ord/first]
  all s: HeThong - Ord/last | Step[s, Ord/next[s]]
}

assert KhongChetDoi_Bounded {
  all p: TrietGia, s: HeThong |
    (s.trangThai[p] = Doi) implies
      some t: HeThong | t in s.*Ord/next and t.trangThai[p] = An
}

run {} for 5 TrietGia, 5 Nia, 10 HeThong
check KhongChetDoi_Bounded for 5 TrietGia, 5 Nia, 100 HeThong
