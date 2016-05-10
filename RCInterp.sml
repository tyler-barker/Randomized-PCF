use "RCParser.sml";

fun getValue (LEAF x) xs = x
|   getValue (NODE (l,r)) nil = BOT
|   getValue (NODE (l,r)) (hd::tl) = if hd then getValue r tl 
                                           else getValue l tl
|   getValue v xs = AST_ERROR ("ERROR")

fun getTree (LEAF x) xs = LEAF x
|   getTree (NODE (l,r)) (hd::tail) = if hd then getTree r tail
                                            else getTree l tail
|   getTree x xs = x

fun tails (LEAF x) = LEAF x
|   tails (NODE (l,r)) = l
|   tails x = x

fun heads (LEAF x) = LEAF x
|   heads (NODE (l,r)) = r
|   heads x = x

fun lazy subst (AST_IF (e1, e2, e3)) x t = AST_IF ((subst e1 x t), 
                                                   (subst e2 x t), 
                                                   (subst e3 x t))
|   subst (AST_APP (e1, e2)) x t = AST_APP ((subst e1 x t), 
                                            (subst e2 x t))
|   subst (LEAF (AST_ID v)) x t = if v=x then t else LEAF (AST_ID v)
|   subst (LEAF (AST_FUN (v, e))) x t = 
           LEAF (AST_FUN (v, if v=x then e else (subst e x t)))
|   subst (LEAF (AST_REC (v, e))) x t = 
           LEAF (AST_REC (v, if v=x then e else (subst e x t))) 
|   subst (NODE (l, r)) x t = NODE ((subst l x t), (subst r x t))
|   subst e _ _ = e

fun lazy interp (LEAF (AST_ID x)) = LEAF (AST_ERROR 
                                   ("unbound identifier: "^x))
|   interp (LEAF (AST_REC (x, e))) = interp 
           (subst e x (LEAF (AST_REC (x, e)))) 
|   interp (AST_IF (e1, e2, e3)) =
   (case (interp e1) of
      (LEAF (AST_ERROR s))    => LEAF (AST_ERROR s)
    | (LEAF (AST_BOOL true))  => interp e2
    | (LEAF (AST_BOOL false)) => interp e3      
    | (NODE (l, r))           => NODE 
                                (tails (interp (AST_IF (l, e2, e3))), 
                                 heads (interp (AST_IF (r, e2, e3))))   
    | (_)                     => LEAF (AST_ERROR 
                                 "if condition must be a bool"))
|   interp (AST_APP (e1, e2)) =
   (case (interp e1, interp e2) of
      (LEAF (AST_ERROR s), _)           => LEAF (AST_ERROR s)
    | (_, LEAF (AST_ERROR s))           => LEAF (AST_ERROR s)
    | (NODE (l, r), NODE (l2, r2))  => NODE 
                                      (tails (interp (AST_APP (l, l2))), 
                                       heads (interp (AST_APP (r, r2))))
    | (f, NODE (l, r))          => NODE (tails (interp (AST_APP (f, l))), 
                                         heads (interp (AST_APP (f, r))))
    | (NODE (l, r), x)          => NODE (tails (interp (AST_APP (l, x))), 
                                         heads (interp (AST_APP (r, x))))
    | (LEAF AST_SUCC, LEAF (AST_NUM n)) => LEAF (AST_NUM (n+1))
    | (LEAF AST_SUCC, _)                => LEAF (AST_ERROR 
                                           "succ needs int argument")
    | (LEAF AST_PRED, LEAF (AST_NUM 0)) => LEAF (AST_NUM 0)
    | (LEAF AST_PRED, LEAF (AST_NUM n)) => LEAF (AST_NUM (n-1))
    | (LEAF AST_PRED, _)                => LEAF (AST_ERROR 
                                           "pred needs int argument")
    | (LEAF AST_PLUS, LEAF (AST_NUM n)) => LEAF (NAT_FUN (fn m=>m+n))
    | (LEAF AST_PLUS, _)                => LEAF (AST_ERROR 
                                           "plus needs int argument")
    | (LEAF AST_MINUS, LEAF (AST_NUM n))=> LEAF (NAT_FUN (fn m=>n-m))
    | (LEAF AST_MINUS, _)               => LEAF (AST_ERROR 
                                           "minus needs int argument")
    | (LEAF AST_MULT, LEAF (AST_NUM n)) => LEAF (NAT_FUN (fn m=>n*m))
    | (LEAF AST_MULT, _)                => LEAF (AST_ERROR 
                                           "mult needs int argument")
    | (LEAF AST_DIV, LEAF (AST_NUM n))  => LEAF (NAT_FUN (fn m=>n div m))
    | (LEAF AST_DIV, _)                 => LEAF (AST_ERROR 
                                           "div needs int argument")
    | (LEAF AST_MOD, LEAF (AST_NUM n))  => LEAF (NAT_FUN (fn m=>n mod m))
    | (LEAF AST_MOD, _)                 => LEAF (AST_ERROR 
                                           "mod needs int argument")
    | (LEAF(NAT_FUN f), LEAF(AST_NUM n))=> LEAF (AST_NUM (f n))
    | (LEAF (NAT_FUN f), _)             => LEAF (AST_ERROR 
                                           "need int argument")
    | (LEAF AST_ISZERO, LEAF(AST_NUM 0))=> LEAF (AST_BOOL true)
    | (LEAF AST_ISZERO, LEAF(AST_NUM _))=> LEAF (AST_BOOL false)
    | (LEAF AST_ISZERO, _)              => LEAF (AST_ERROR 
                                           "iszero needs int argument")
    | (LEAF (AST_FUN (x, e)), v)        => interp (subst e x v)                               
    | (_, _)                            => LEAF (AST_ERROR 
                                           "not a functional application"))
|   interp (NODE (l, r)) = NODE ((interp l), (interp r))
|   interp e = e

val rng = Random.rand(0,1)

fun rc_interp t = 
    (case (interp t) of
        (LEAF x)            => LEAF x
      | (NODE (l,r))        => (case (Random.randRange (0,1) rng) of
            0               => rc_interp l
          | _               => rc_interp r)
      | e                   => e)
          
fun rc_interp_n t n = if n = 0 then getValue t nil else
    (case (interp t) of
        (LEAF x)            => x
      | (NODE (l,r))        => (case (Random.randRange (0,1) rng) of
            0               => rc_interp_n l (n-1)
          | _               => rc_interp_n r (n-1))
      | e                   => getValue e nil)
          
fun rc_tree_n t n = if n = 0 then LEAF (getValue (interp t) nil)
            else (case (interp t) of
                  (LEAF x)   => LEAF x
                | (NODE (l, r)) => NODE (rc_tree_n l (n-1), 
                                         rc_tree_n r (n-1))
                | x => (LEAF (AST_NUM 42)))  

fun rc_tree file n = rc_tree_n (parsefile file) n

fun rc file = getValue (rc_interp (parsefile file)) nil

fun rc_n file n = rc_interp_n (parsefile file) n

