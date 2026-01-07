# PhuongPhapHinhThuc

---

## 0) Alloy là gì? Nó hoạt động kiểu nào?

Alloy là công cụ mô hình hoá (modeling) và kiểm chứng (model checking) dựa trên logic quan hệ (relational logic).

* **Bạn không viết chương trình chạy như Java:**
* Bạn mô tả một “thế giới” gồm các đối tượng (triết gia, nĩa, trạng thái…) và các ràng buộc (constraints) mà thế giới đó phải thỏa.


* **Alloy dùng SAT solver để:**
* `run`: tìm một mô hình cụ thể thỏa toàn bộ ràng buộc (sig, fact, pred...).
* `check`: kiểm tra một assertion bằng cách tìm phản ví dụ (counterexample).
* Nếu tìm được phản ví dụ → assertion invalid.


* **Bounded scope (phạm vi hữu hạn):**
* Alloy chỉ kiểm tra trong phạm vi bạn đặt.
* Ví dụ: `for 5 TrietGia, 5 Nia, 10 HeThong` nghĩa là chỉ xét các mô hình có đúng 5 triết gia, 5 nĩa và 10 snapshot hệ thống (10 thời điểm).



---

## 1) Ý nghĩa tổng thể của mô hình Dining Philosophers

Mô hình mô tả:

* 5 triết gia ngồi quanh bàn tròn, mỗi người có 2 nĩa kề (trái/phải).
* Hệ thống thay đổi theo thời gian: mỗi `HeThong` là một snapshot, và các snapshot nối với nhau thành trace.
* Mỗi bước thời gian, một triết gia thực hiện một hành động:
* `SuyNghi` → `Doi`
* `Doi` → `An` (nếu 2 nĩa rảnh)
* `An` → `SuyNghi` (nhả nĩa)



**Mục tiêu kiểm chứng:**

* Kiểm tra tính chất “không chết đói” (bounded): nếu một triết gia đang đói ở một thời điểm nào đó, thì trong tương lai của trace sẽ có lúc ăn.

---

## 2) Code và giải thích theo từng phần

### 2.1. module và ordering (mô hình thời gian)

```alloy
module DiningPhilosophers_Tutorial
open util/ordering[HeThong] as Ord

```

* `module ...`: đặt tên mô-đun.
* `open util/ordering[HeThong] as Ord`: tạo thứ tự tuyến tính trên các HeThong:
* `Ord/first`: snapshot đầu
* `Ord/last`: snapshot cuối
* `Ord/next[s]`: snapshot kế tiếp của s
* → dùng để tạo trace `s0 -> s1 -> s2 -> ...`



### 2.2. Thực thể: triết gia và nĩa

```alloy
sig TrietGia { niaTrai, niaPhai: one Nia }
sig Nia {}

```

* `sig`: khai báo một tập đối tượng (giống “kiểu”/“class”).
* `niaTrai, niaPhai: one Nia`:
* `one` = “đúng 1”
* mỗi triết gia có đúng 1 nĩa trái và đúng 1 nĩa phải.



### 2.3. Ràng buộc bàn tròn hợp lệ

```alloy
fact BanTron {
  #TrietGia = 5
  #Nia = 5
  all p: TrietGia | p.niaTrai != p.niaPhai
  all n: Nia | one pL: TrietGia | pL.niaTrai = n
  all n: Nia | one pR: TrietGia | pR.phai = n
}

```

* `fact`: ràng buộc luôn đúng.
* `#X`: kích thước tập X (số phần tử).
* `all p: TrietGia | ...`: “với mọi p”.
* `!=`: khác nhau.
* `one pL: TrietGia | ...`: tồn tại đúng 1 phần tử thỏa điều kiện.
* **Ý nghĩa:** đúng 5 triết gia, 5 nĩa; mỗi người có 2 nĩa khác nhau; mỗi nĩa xuất hiện đúng 1 lần ở vai trò “nĩa trái của ai đó” và đúng 1 lần ở “nĩa phải của ai đó” → tạo cấu trúc vòng.

### 2.4. Trạng thái triết gia: suy nghĩ / đói / ăn

```alloy
abstract sig TrangThai {}
one sig SuyNghi, Doi, An extends TrangThai {}

```

* `abstract sig`: không có giá trị nào khác ngoài các extends.
* `one sig`: singleton (mỗi trạng thái là đúng 1 đối tượng).
* `extends`: thuộc kiểu TrangThai.

### 2.5. Snapshot hệ thống theo thời gian: HeThong

```alloy
sig HeThong {
  trangThai: TrietGia -> one TrangThai,
  hold: Nia -> lone TrietGia
}

```

* `->`: quan hệ ánh xạ.
* `trangThai`: mỗi triết gia có đúng 1 trạng thái tại snapshot đó.
* `hold`: mỗi nĩa đang được cầm bởi 0 hoặc 1 triết gia (`lone` = “tối đa 1”).

### 2.6. Hàm cam: triết gia đang cầm nĩa nào

```alloy
fun cam[s: HeThong, p: TrietGia]: set Nia { (s.hold).p }

```

* `fun`: hàm trả về biểu thức.
* `set Nia`: trả về một tập nĩa.
* Dấu `.` trong Alloy là phép join (kết quan hệ).
* `(s.hold).p` = tập các nĩa n sao cho (n -> p) thuộc s.hold → “các nĩa mà p đang cầm tại snapshot s”.

### 2.7. Các bất biến (Invariants)

```alloy
fact Invariants {
  all s: HeThong, p: TrietGia |
    (s.trangThai[p] = An) iff
      (p.niaTrai.(s.hold) = p and p.niaPhai.(s.hold) = p)

  all s: HeThong, p: TrietGia |
    s.trangThai[p] = SuyNghi implies no cam[s, p]
}

```

* `iff`: tương đương hai chiều.
* `implies`: kéo theo (nếu ... thì ...).
* `no X`: X rỗng.
* **Ý nghĩa:** Ăn ↔ cầm đủ 2 nĩa của mình; Suy nghĩ → không cầm nĩa.

### 2.8. Trạng thái ban đầu

```alloy
pred Init[s: HeThong] {
  all p: TrietGia | s.trangThai[p] = SuyNghi
  no s.hold
}

```

* `pred`: predicate (điều kiện).
* **Ban đầu:** mọi người suy nghĩ, không ai cầm nĩa.

---

## 3) Chuyển trạng thái theo bước (Transitions)

### 3.1. BecomeHungry: Suy nghĩ → Đói

* `p` đang suy nghĩ → sang đói.
* Việc “đói” không làm thay đổi việc cầm nĩa.
* `s2.trangThai = s.trangThai ++ (p -> Doi)` (`++` là override).

### 3.2. StartEating: Đói → Ăn nếu 2 nĩa rảnh

* `p` đang đói.
* Hai nĩa của `p` đều rảnh (`no ...` nghĩa là không ai đang giữ).
* `p` cầm cả 2 nĩa và chuyển sang `An`.

### 3.3. FinishEating: Ăn → Suy nghĩ, nhả nĩa

* `p` đang `An`.
* `s2.hold = s.hold - (p.niaTrai -> TrietGia) ...` (`-` là loại bỏ cặp khỏi quan hệ).
* Giải phóng nĩa và quay lại trạng thái `SuyNghi`.

### 3.4. Step: mỗi bước chọn 1 triết gia làm 1 hành động

* Mỗi bước, hệ thống được quyền chọn một triết gia và thực hiện một chuyển trạng thái hợp lệ.

---

## 4) Trace: nối các snapshot thành chuỗi thời gian

* Snapshot đầu phải thỏa `Init`.
* Mọi snapshot trừ snapshot cuối phải có bước chuyển hợp lệ sang snapshot tiếp theo.

---

## 5) Assertion “không chết đói” (bounded liveness)

* `s.*Ord/next`: tập các trạng thái reachable từ `s` bằng 0 hoặc nhiều bước `next`.
* **Ý nghĩa:** nếu ở thời điểm `s`, `p` đang đói → phải tồn tại một thời điểm `t` ở hiện tại/tương lai mà `p` đang ăn.

---

## 6) run / check và “HeThong = 100” nghĩa là gì?

* `run {} for 5 TrietGia, 5 Nia, 10 HeThong`
* `check KhongChetDoi_Bounded for 5 TrietGia, 5 Nia, 100 HeThong`
* **HeThong** là số snapshot thời gian trong trace:
* 10 HeThong: trace dài 10 trạng thái.
* 100 HeThong: trace dài 100 trạng thái.



---

## 7) Tại sao tăng lên 100 HeThong vẫn “invalid”?

Vì mô hình không có fairness (công bằng lịch). Trong `Step`, Alloy có thể chọn triết gia bất kỳ ở mỗi bước và hoàn toàn có thể tạo trace mà:

* Một triết gia `p` chuyển sang `Doi`.
* Từ đó về sau, hệ thống không bao giờ chọn `p` để thực hiện `StartEating`.
* Các triết gia khác vẫn có thể ăn luân phiên.
* → `p` đói mãi đến hết trace, dù trace dài 10 hay 100.
* **Kết luận formal:** Mô hình này tránh deadlock (chỉ ăn khi có đủ 2 nĩa), nhưng không đảm bảo starvation-free nếu không thêm fairness.

---

## 8) Vì sao cần thêm trạng thái ĐÓI (Hungry / Doi)?

Dù đề bài không ghi chữ “đói”, nhưng để kiểm tra “chết đói” thì bắt buộc phải có một trạng thái thể hiện yêu cầu ăn.

* **8.1. Starvation là khái niệm theo thời gian:** “Chết đói” nghĩa là: Muốn ăn nhưng không bao giờ được ăn. Nó không phải “không ăn”, vì “không ăn” có thể là “không muốn ăn”.
* **8.2. Nếu không có Doi, không thể phân biệt:** “không ăn vì đang suy nghĩ” và “không ăn dù đã yêu cầu ăn”. Do đó, không thể phát biểu đúng starvation.
* **8.3. Dạng chuẩn trong logic thời gian:** Starvation-free thường viết dạng `Hungry(p) -> eventually Eating(p)`. Trong Alloy (bounded), chính là: `Doi` -> tồn tại trạng thái tương lai `An`. Nếu bỏ `Doi`, bạn mất “điểm bắt đầu” để nói “eventually”.

---

Bạn có muốn tôi hỗ trợ thêm về cách tạo các biểu đồ (Visualizer) trong Alloy để minh họa cho file README này không?
