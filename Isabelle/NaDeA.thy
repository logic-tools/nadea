theory NaDeA imports Main begin

type_synonym id = "char list"

datatype tm = Var nat | Fun id "tm list"

datatype fm = Falsity | Pre id "tm list" | Imp fm fm | Dis fm fm | Con fm fm | Exi fm | Uni fm

primrec
  semantics_term :: "(nat \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm \<Rightarrow> 'a"
and
  semantics_list :: "(nat \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm list \<Rightarrow> 'a list"
where
  "semantics_term e f (Var n) = e n" |
  "semantics_term e f (Fun i l) = f i (semantics_list e f l)" |
  "semantics_list e f [] = []" |
  "semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l"

primrec
  semantics :: "(nat \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> fm \<Rightarrow> bool"
where
  "semantics e f g Falsity = False" |
  "semantics e f g (Pre i l) = g i (semantics_list e f l)" |
  "semantics e f g (Imp p q) = (if semantics e f g p then semantics e f g q else True)" |
  "semantics e f g (Dis p q) = (if semantics e f g p then True else semantics e f g q)" |
  "semantics e f g (Con p q) = (if semantics e f g p then semantics e f g q else False)" |
  "semantics e f g (Exi p) = (\<exists>x. semantics (\<lambda>n. if n = 0 then x else e (n - 1)) f g p)" |
  "semantics e f g (Uni p) = (\<forall>x. semantics (\<lambda>n. if n = 0 then x else e (n - 1)) f g p)"

primrec
  member :: "fm \<Rightarrow> fm list \<Rightarrow> bool"
where
  "member p [] = False" |
  "member p (q # z) = (if p = q then True else member p z)"

primrec
  new_term :: "id \<Rightarrow> tm \<Rightarrow> bool"
and
  new_list :: "id \<Rightarrow> tm list \<Rightarrow> bool"
where
  "new_term c (Var n) = True" |
  "new_term c (Fun i l) = (if i = c then False else new_list c l)" |
  "new_list c [] = True" |
  "new_list c (t # l) = (if new_term c t then new_list c l else False)"

primrec
  new :: "id \<Rightarrow> fm \<Rightarrow> bool"
where
  "new c Falsity = True" |
  "new c (Pre i l) = new_list c l" |
  "new c (Imp p q) = (if new c p then new c q else False)" |
  "new c (Dis p q) = (if new c p then new c q else False)" |
  "new c (Con p q) = (if new c p then new c q else False)" |
  "new c (Exi p) = new c p" |
  "new c (Uni p) = new c p"

primrec
  news :: "id \<Rightarrow> fm list \<Rightarrow> bool"
where
  "news c [] = True" |
  "news c (p # z) = (if new c p then news c z else False)"

primrec
  inc_term :: "tm \<Rightarrow> tm"
and
  inc_list :: "tm list \<Rightarrow> tm list"
where
  "inc_term (Var n) = Var (n + 1)" |
  "inc_term (Fun i l) = Fun i (inc_list l)" |
  "inc_list [] = []" |
  "inc_list (t # l) = inc_term t # inc_list l"

primrec
  sub_term :: "nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"
and
  sub_list :: "nat \<Rightarrow> tm \<Rightarrow> tm list \<Rightarrow> tm list"
where
  "sub_term v s (Var n) = (if n < v then Var n else if n = v then s else Var (n - 1))" |
  "sub_term v s (Fun i l) = Fun i (sub_list v s l)" |
  "sub_list v s [] = []" |
  "sub_list v s (t # l) = sub_term v s t # sub_list v s l"

primrec
  sub :: "nat \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> fm"
where
  "sub v s Falsity = Falsity" |
  "sub v s (Pre i l) = Pre i (sub_list v s l)" |
  "sub v s (Imp p q) = Imp (sub v s p) (sub v s q)" |
  "sub v s (Dis p q) = Dis (sub v s p) (sub v s q)" |
  "sub v s (Con p q) = Con (sub v s p) (sub v s q)" |
  "sub v s (Exi p) = Exi (sub (v + 1) (inc_term s) p)" |
  "sub v s (Uni p) = Uni (sub (v + 1) (inc_term s) p)"

inductive
  OK :: "fm \<Rightarrow> fm list \<Rightarrow> bool"
where
Assume:
        "member p z \<Longrightarrow> OK p z" |
Boole:
        "OK Falsity ((Imp p Falsity) # z) \<Longrightarrow> OK p z" |
Imp_E:
        "OK (Imp p q) z \<Longrightarrow> OK p z \<Longrightarrow> OK q z" |
Imp_I:
        "OK q (p # z) \<Longrightarrow> OK (Imp p q) z" |
Dis_E:
        "OK (Dis p q) z \<Longrightarrow> OK r (p # z) \<Longrightarrow> OK r (q # z) \<Longrightarrow> OK r z" |
Dis_I1:
        "OK p z \<Longrightarrow> OK (Dis p q) z" |
Dis_I2:
        "OK q z \<Longrightarrow> OK (Dis p q) z" |
Con_E1:
        "OK (Con p q) z \<Longrightarrow> OK p z" |
Con_E2:
        "OK (Con p q) z \<Longrightarrow> OK q z" |
Con_I:
        "OK p z \<Longrightarrow> OK q z \<Longrightarrow> OK (Con p q) z" |
Exi_E:
        "OK (Exi p) z \<Longrightarrow> OK q ((sub 0 (Fun c []) p) # z) \<Longrightarrow> news c (p # q # z) \<Longrightarrow> OK q z" |
Exi_I:
        "OK (sub 0 t p) z \<Longrightarrow> OK (Exi p) z" |
Uni_E:
        "OK (Uni p) z \<Longrightarrow> OK (sub 0 t p) z" |
Uni_I:
        "OK (sub 0 (Fun c []) p) z \<Longrightarrow> news c (p # z) \<Longrightarrow> OK (Uni p) z"

lemma "OK (Imp (Pre ''A'' []) (Pre ''A'' [])) []" proof (rule Imp_I, rule Assume, simp) qed

lemma "OK (Imp (Pre ''A'' []) (Pre ''A'' [])) []"
proof -
  have "OK (Pre ''A'' []) [(Pre ''A'' [])]" proof (rule Assume) qed simp
  then show "OK (Imp (Pre ''A'' []) (Pre ''A'' [])) []" proof (rule Imp_I) qed
qed

fun
  put :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
where
  "put e v x = (\<lambda>n. if n < v then e n else if n = v then x else e (n - 1))"

lemma "put e 0 x = (\<lambda>n. if n = 0 then x else e (n - 1))" proof simp qed

lemma increment:
  "semantics_term (put e 0 x) f (inc_term t) = semantics_term e f t"
  "semantics_list (put e 0 x) f (inc_list l) = semantics_list e f l"
proof (induct t and l rule: semantics_term.induct semantics_list.induct) qed simp_all

lemma commute: "put (put e v x) 0 y = put (put e 0 y) (v + 1) x" proof force qed

fun
  all :: "(fm \<Rightarrow> bool) \<Rightarrow> fm list \<Rightarrow> bool"
where
  "all b z = (\<forall>p. if member p z then b p else True)"

lemma allhead: "all b (p # z) \<Longrightarrow> b p" proof simp qed

lemma alltail: "all b (p # z) \<Longrightarrow> all b z" proof simp qed

lemma allnew: "all (new c) z = news c z" proof (induct z) qed (simp, simp, metis)

lemma map':
  "new_term c t \<Longrightarrow> semantics_term e (f(c := m)) t = semantics_term e f t"
  "new_list c l \<Longrightarrow> semantics_list e (f(c := m)) l = semantics_list e f l"
proof (induct t and l rule: semantics_term.induct semantics_list.induct)
qed (simp, simp, metis, simp, simp, metis)

lemma map: "new c p \<Longrightarrow> semantics e (f(c := m)) g p = semantics e f g p"
proof (induct p arbitrary: e)
qed (simp, simp, metis map'(2), simp, metis, simp, metis, simp, metis, simp_all)

lemma allmap: "news c z \<Longrightarrow> all (semantics e (f(c := m)) g) z = all (semantics e f g) z"
proof (induct z) qed (simp, simp, metis map)

lemma substitute':
  "semantics_term e f (sub_term v s t) = semantics_term (put e v (semantics_term e f s)) f t"
  "semantics_list e f (sub_list v s l) = semantics_list (put e v (semantics_term e f s)) f l"
proof (induct t and l rule: semantics_term.induct semantics_list.induct) qed simp_all

lemma substitute: "semantics e f g (sub v t p) = semantics (put e v (semantics_term e f t)) f g p"
proof (induct p arbitrary: e v t)
  fix i l e v t
  show "semantics e f g (sub v t (Pre i l)) =
      semantics (put e v (semantics_term e f t)) f g (Pre i l)"
  proof (simp add: substitute'(2)) qed
next
  fix p e v t assume *: "semantics e' f g (sub v' t' p) =
      semantics (put e' v' (semantics_term e' f t')) f g p" for e' v' t'
  have "semantics e f g (sub v t (Exi p)) =
      (\<exists>x. semantics (put (put e 0 x) (v + 1) (semantics_term (put e 0 x) f (inc_term t))) f g p)"
    using * proof simp qed
  also have "... = (\<exists>x. semantics (put (put e v (semantics_term e f t)) 0 x) f g p)"
    using commute increment(1) proof metis qed
  finally show "semantics e f g (sub v t (Exi p)) =
      semantics (put e v (semantics_term e f t)) f g (Exi p)" proof simp qed
  have "semantics e f g (sub v t (Uni p)) =
      (\<forall>x. semantics (put (put e 0 x) (v + 1) (semantics_term (put e 0 x) f (inc_term t))) f g p)"
    using * proof simp qed
  also have "... = (\<forall>x. semantics (put (put e v (semantics_term e f t)) 0 x) f g p)"
    using commute increment(1) proof metis qed
  finally show "semantics e f g (sub v t (Uni p)) =
      semantics (put e v (semantics_term e f t)) f g (Uni p)" proof simp qed
qed simp_all

lemma soundness': "OK p z \<Longrightarrow> all (semantics e f g) z \<Longrightarrow> semantics e f g p"
proof (induct arbitrary: f rule: OK.induct)
  fix f p z assume "all (semantics e f g) z"
      "all (semantics e f' g) (Imp p Falsity # z) \<Longrightarrow> semantics e f' g Falsity" for f'
  then show "semantics e f g p" proof force qed
next
  fix f p q z r assume "all (semantics e f g) z"
      "all (semantics e f' g) z \<Longrightarrow> semantics e f' g (Dis p q)"
      "all (semantics e f' g) (p # z) \<Longrightarrow> semantics e f' g r"
      "all (semantics e f' g) (q # z) \<Longrightarrow> semantics e f' g r" for f'
  then show "semantics e f g r" proof (simp, metis) qed
next
  fix f p q z assume "all (semantics e f g) z"
      "all (semantics e f' g) z \<Longrightarrow> semantics e f' g (Con p q)" for f'
  then show "semantics e f g p" "semantics e f g q" proof (simp, metis, simp, metis) qed
next
  fix f p z q c assume *: "all (semantics e f g) z"
      "all (semantics e f' g) z \<Longrightarrow> semantics e f' g (Exi p)"
      "all (semantics e f' g) (sub 0 (Fun c []) p # z) \<Longrightarrow> semantics e f' g q"
      "news c (p # q # z)" for f'
  obtain x where "semantics (\<lambda>n. if n = 0 then x else e (n - 1)) f g p"
    using *(1) *(2) proof force qed
  then have "semantics (put e 0 x) f g p" proof simp qed
  then have "semantics (put e 0 x) (f(c := \<lambda>w. x)) g p"
    using *(4) allhead allnew map proof blast qed
  then have "semantics e (f(c := \<lambda>w. x)) g (sub 0 (Fun c []) p)"
    proof (simp add: substitute) qed
  moreover have "all (semantics e (f(c := \<lambda>w. x)) g) z"
    using *(1) *(4) alltail allnew allmap proof blast qed
  ultimately have "semantics e (f(c := \<lambda>w. x)) g q" using *(3) proof simp qed
  then show "semantics e f g q" using *(4) allhead alltail allnew map proof blast qed
next
  fix f z t p assume "all (semantics e f g) z"
      "all (semantics e f' g) z \<Longrightarrow> semantics e f' g (sub 0 t p)" for f'
  then have "semantics (put e 0 (semantics_term e f t)) f g p" proof (simp add: substitute) qed
  then show "semantics e f g (Exi p)" proof (simp, metis) qed
next
  fix f z t p assume "all (semantics e f g) z"
      "all (semantics e f' g) z \<Longrightarrow> semantics e f' g (Uni p)" for f'
  then show "semantics e f g (sub 0 t p)" proof (simp add: substitute) qed
next
  fix f c p z assume *: "all (semantics e f g) z"
      "all (semantics e f' g) z \<Longrightarrow> semantics e f' g (sub 0 (Fun c []) p)"
      "news c (p # z)" for f'
  have "semantics (\<lambda>n. if n = 0 then x else e (n - 1)) f g p" for x
  proof -
    have "all (semantics e (f(c := \<lambda>w. x)) g) z"
      using *(1) *(3) alltail allnew allmap proof blast qed
    then have "semantics e (f(c := \<lambda>w. x)) g (sub 0 (Fun c []) p)"
      using *(2) proof simp qed
    then have "semantics (\<lambda>n. if n = 0 then x else e (n - 1)) (f(c := \<lambda>w. x)) g p"
      proof (simp add: substitute) qed
    then show "semantics (\<lambda>n. if n = 0 then x else e (n - 1)) f g p"
      using *(3) allhead alltail allnew map proof blast qed
  qed
  then show "semantics e f g (Uni p)" proof simp qed
qed simp_all

theorem soundness: "OK p [] \<Longrightarrow> semantics e f g p" proof (simp add: soundness') qed

corollary "\<exists>p. OK p []" "\<exists>p. \<not> OK p []"
proof -
  have "OK (Imp p p) []" for p proof (rule Imp_I, rule Assume, simp) qed
  then show "\<exists>p. OK p []" proof iprover qed
next
  have "\<not> semantics (e :: nat \<Rightarrow> unit) f g Falsity" for e f g proof simp qed
  then show "\<exists>p. \<not> OK p []" using soundness proof iprover qed
qed

end
