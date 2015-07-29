theory NaDeA imports Main begin

type_synonym id = string

datatype tm = Var nat | Fun id "tm list"

datatype fm = Falsity | Pre id "tm list" | Imp fm fm | Dis fm fm | Con fm fm | Exi fm | Uni fm

primrec
  semantics_term :: "(nat => 'u) => (id => 'u list => 'u) => tm => 'u"
and
  semantics_list :: "(nat => 'u) => (id => 'u list => 'u) => tm list => 'u list"
where
  "semantics_term e f (Var v) = e v" |
  "semantics_term e f (Fun i l) = f i (semantics_list e f l)" |
  "semantics_list e f [] = []" |
  "semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l"

primrec
  semantics :: "(nat => 'u) => (id => 'u list => 'u) => (id => 'u list => bool) => fm => bool"
where
  "semantics e f g Falsity = False" |
  "semantics e f g (Pre i l) = g i (semantics_list e f l)" |
  "semantics e f g (Imp p q) = (if semantics e f g p then semantics e f g q else True)" |
  "semantics e f g (Dis p q) = (if semantics e f g p then True else semantics e f g q)" |
  "semantics e f g (Con p q) = (if semantics e f g p then semantics e f g q else False)" |
  "semantics e f g (Exi p) = (? x. semantics (% n. if n = 0 then x else e (n - 1)) f g p)" |
  "semantics e f g (Uni p) = (! x. semantics (% n. if n = 0 then x else e (n - 1)) f g p)"

primrec
  member :: "fm => fm list => bool"
where
  "member p [] = False" |
  "member p (q # a) = (if p = q then True else member p a)"

primrec
  new_term :: "id => tm => bool"
and
  new_list :: "id => tm list => bool"
where
  "new_term c (Var v) = True" |
  "new_term c (Fun i l) = (if i = c then False else new_list c l)" |
  "new_list c [] = True" |
  "new_list c (t # l) = (if new_term c t then new_list c l else False)"

primrec
  new :: "id => fm => bool"
where
  "new c Falsity = True" |
  "new c (Pre i l) = new_list c l" |
  "new c (Imp p q) = (if new c p then new c q else False)" |
  "new c (Dis p q) = (if new c p then new c q else False)" |
  "new c (Con p q) = (if new c p then new c q else False)" |
  "new c (Exi p) = new c p" |
  "new c (Uni p) = new c p"

primrec
  news :: "id => fm list => bool"
where
  "news c [] = True" |
  "news c (p # a) = (if new c p then news c a else False)"

primrec
  inc_term :: "tm => tm"
and
  inc_list :: "tm list => tm list"
where
  "inc_term (Var v) = Var (v + 1)" |
  "inc_term (Fun i l) = Fun i (inc_list l)" |
  "inc_list [] = []" |
  "inc_list (t # l) = inc_term t # inc_list l"

primrec
  sub_term :: "nat => tm => tm => tm"
and
  sub_list :: "nat => tm => tm list => tm list"
where
  "sub_term n s (Var v) = (if v = n then s else if v > n then Var (v - 1) else Var v)" |
  "sub_term n s (Fun i l) = Fun i (sub_list n s l)" |
  "sub_list n s [] = []" |
  "sub_list n s (t # l) = sub_term n s t # sub_list n s l"

primrec
  sub :: "nat => tm => fm => fm"
where
  "sub n s Falsity = Falsity" |
  "sub n s (Pre i l) = Pre i (sub_list n s l)" |
  "sub n s (Imp p q) = Imp (sub n s p) (sub n s q)" |
  "sub n s (Dis p q) = Dis (sub n s p) (sub n s q)" |
  "sub n s (Con p q) = Con (sub n s p) (sub n s q)" |
  "sub n s (Exi p) = Exi (sub (n + 1) (inc_term s) p)" |
  "sub n s (Uni p) = Uni (sub (n + 1) (inc_term s) p)"

inductive
  OK :: "fm => fm list => bool"
where
Assume:
        "member p a ==> OK p a" |
Boole:
        "OK Falsity ((Imp p Falsity) # a) ==> OK p a" |
Imp_E:
        "OK (Imp p q) a ==> OK p a ==> OK q a" |
Imp_I:
        "OK q (p # a) ==> OK (Imp p q) a" |
Dis_E:
        "OK (Dis p q) a ==> OK r (p # a) ==> OK r (q # a) ==> OK r a" |
Dis_I1:
        "OK p a ==> OK (Dis p q) a" |
Dis_I2:
        "OK q a ==> OK (Dis p q) a" |
Con_E1:
        "OK (Con p q) a ==> OK p a" |
Con_E2:
        "OK (Con p q) a ==> OK q a" |
Con_I:
        "OK p a ==> OK q a ==> OK (Con p q) a" |
Exi_E:
        "OK (Exi p) a ==> OK q ((sub 0 (Fun c []) p) # a) ==> news c (p # q # a) ==> OK q a" |
Exi_I:
        "OK (sub 0 t p) a ==> OK (Exi p) a" |
Uni_E:
        "OK (Uni p) a ==> OK (sub 0 t p) a" |
Uni_I:
        "OK (sub 0 (Fun c []) p) a ==> news c (p # a) ==> OK (Uni p) a"

fun
  put :: "(nat => 'u) => nat => 'u => nat => 'u"
where
  "put e i x = (% n. if n < i then e n else if n = i then x else e (n - 1))"

lemma put_special: "(% n. if n = 0 then x else e (n - 1)) = put e 0 x"
by simp

lemma newness: "news c (p # a) ==> new c p" "news c (p # a) ==> news c a"
by simp_all metis+

lemma membership: "member p a ==> p : set a"
by (induct a, simp_all) metis

lemma update':
  "new_term n t ==> semantics_term e (f(n := x)) t = semantics_term e f t"
  "new_list n l ==> semantics_list e (f(n := x)) l = semantics_list e f l"
by (induct t and l rule: semantics_term.induct semantics_list.induct, simp_all) metis+

lemma update: "new n p ==> semantics e (f(n := x)) g p = semantics e f g p"
by (induct p arbitrary: e, simp_all add: update') metis+

lemma list_update:
  "news n a ==> list_all (semantics e (f(n := x)) g) a = list_all (semantics e f g) a"
by (induct a, simp_all, metis update)

lemma put_commute: "put (put e i x) 0 y = put (put e 0 y) (i + 1) x"
by force

lemma increment:
  "semantics_term (put e 0 x) f (inc_term t) = semantics_term e f t"
  "semantics_list (put e 0 x) f (inc_list l) = semantics_list e f l"
by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma substitute':
  "semantics_term e f (sub_term i u t) = semantics_term (put e i (semantics_term e f u)) f t"
  "semantics_list e f (sub_list i u l) = semantics_list (put e i (semantics_term e f u)) f l"
by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma substitute: "semantics e f g (sub i t a) = semantics (put e i (semantics_term e f t)) f g a"
proof (induct a arbitrary: e t i)
  case (Pre p l)
  show ?case by (simp add: substitute')
next
  case (Uni a)
  have "semantics (put e i (semantics_term e f t)) f g (Uni a)
            = (! x. semantics (put (put e i (semantics_term e f t)) 0 x) f g a)"
    by simp
  also
  have "... = (! x. semantics (put (put e 0 x) (i + 1) (semantics_term e f t)) f g a)" 
    unfolding put_commute by simp
  also
  have "... = (! x. semantics
            (put (put e 0 x) (i + 1) (semantics_term (put e 0 x) f (inc_term t))) f g a)"
    unfolding increment by simp
  also
  have "... = (! x. semantics (put e 0 x) f g (sub (i + 1) (inc_term t) a))" using Uni by simp
  also
  have "... = semantics e f g (Uni (sub (i + 1) (inc_term t) a))" by simp
  also
  have "... = semantics e f g (sub i t (Uni a))" by simp
  finally show ?case by simp
next
  case (Exi a)
  have "semantics (put e i (semantics_term e f t)) f g (Exi a)
            = (? x. semantics (put (put e i (semantics_term e f t)) 0 x) f g a)" by simp
  also
  have "... = (? x. semantics (put (put e 0 x) (i + 1) (semantics_term e f t)) f g a)" 
    unfolding put_commute by simp
  also
  have "... = (? x. semantics
            (put (put e 0 x) (i + 1) (semantics_term (put e 0 x) f (inc_term t))) f g a)"
    unfolding increment by simp
  also
  have "... = (? x. semantics (put e 0 x) f g (sub (i + 1) (inc_term t) a))" using Exi by simp
  also
  have "... = semantics e f g (Exi (sub (i + 1) (inc_term t) a))" by simp
  finally show ?case by simp
qed simp_all

lemma soundness': "OK p a ==> list_all (semantics e f g) a ==> semantics e f g p"
proof (induct arbitrary: e f rule: OK.induct)
  case (Assume p a)
  then have "p : set a" using membership by simp
  moreover
  from Assume have "p : set a ==> semantics e f g p" unfolding list_all_iff by simp
  ultimately show ?case by simp
next
  case (Boole p a)
  then show ?case by simp metis
next
  case (Dis_E p q a r)
  then show ?case by simp metis
next
  case (Con_E1 p q a)
  then show ?case by simp metis
next
  case (Con_E2 p q a)
  then show ?case by simp metis
next
  case (Exi_I t p a)
  then have "semantics e f g (sub 0 t p)" by simp
  then have "semantics (% n. if n = 0 then semantics_term e f t else e (n - 1)) f g p"
    unfolding substitute by simp
  then have "(? x. semantics (% n. if n = 0 then x else e (n - 1)) f g p)" by metis
  then show ?case by simp
next
  case (Uni_E p a t)
  then have "semantics e f g (Uni p)" by simp
  then have "! x. semantics (% n. if n = 0 then x else e (n - 1)) f g p" by simp
  then have "semantics (% n. if n = 0 then semantics_term e f t else e (n - 1)) f g p" by simp
  then show ?case unfolding substitute by simp
next
  case (Exi_E p a q c)
  let ?upd = "% e x.(% n. if n = 0 then x else e (n - 1))"
  from Exi_E have "semantics e f g (Exi p)" by simp
  then have "(? z. semantics (?upd e z) f g p)" by simp
  then obtain z where z_def: "semantics (?upd e z) f g p" by metis
  let ?f' = "f(c := % x. z)"
  from z_def have "semantics (put e 0 z) f g p" by simp
  then have "semantics (put e 0 z) ?f' g p" using Exi_E update newness by metis
  then have "semantics (put e 0 (semantics_term e ?f' (Fun c [])))?f' g p" by simp
  then have p_holds: "semantics e ?f' g (sub 0 (Fun c []) p)" unfolding substitute by simp
  then have a_holds: "list_all (semantics e ?f' g) a" using Exi_E list_update newness by metis
  then have "semantics e ?f' g q" using Exi_E p_holds a_holds by simp
  then show ?case using Exi_E update newness by metis
next
  case (Uni_I c p a)
  let ?upd = "% e x.(% n. if n = 0 then x else e (n - 1))"
  have "! x. semantics (?upd e x) f g p"
    proof
      fix x
      let ?f' = "f(c := % y. x)"
      from Uni_I have "list_all (semantics e ?f' g) a" using list_update newness by metis
      then have "semantics e ?f' g (sub 0 (Fun c []) p)" using Uni_I by simp
      then have "semantics (?upd e (semantics_term e ?f' (Fun c []))) ?f' g p"
        unfolding put_special substitute by simp
      then have "semantics (?upd e (?f' c (semantics_list e ?f' []))) ?f' g p"
        unfolding put_special by simp
      then have "semantics (?upd e x) ?f' g p" using fun_upd_apply by metis
      then show "semantics (?upd e x) f g p" using Uni_I update newness by blast
    qed
  then show ?case by simp
qed simp_all

theorem soundness: "OK p [] ==> semantics e f g p"
using soundness' by force

end
