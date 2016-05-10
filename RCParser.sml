Control.Print.printDepth:= 100;
Control.lazysml := true;
open Lazy;

datatype term = AST_ID of string | AST_NUM of int | AST_BOOL of bool 
        | AST_ERROR of string | BOT | NAT_FUN of (int -> int)
        | AST_FUN of (string * rc_term) | AST_REC of (string * rc_term) 
        | AST_SUCC | AST_PRED | AST_ISZERO
        | AST_PLUS | AST_MINUS | AST_MULT | AST_DIV | AST_MOD
and lazy rc_term = LEAF of term
                 | AST_APP of (rc_term * rc_term) 
                 | AST_IF of (rc_term * rc_term * rc_term) 
                 | NODE of (rc_term * rc_term)
  
datatype token = ID of string | NUM of int 
  | IFSYM | THENSYM | ELSESYM | BOTSYM | TRUESYM | FALSESYM 
  | SUCCSYM | PREDSYM | ISZEROSYM | FNSYM | RECSYM 
  | EQUAL | LPAREN | RPAREN | FNARROW | LETSYM | INSYM | ENDSYM | EOF
  | RC | VERT | LBRACE | RBRACE | PLUS | MINUS | MULT | DIV | MOD
  
signature PCFLEXER =
sig
    val lexfile : string -> token list
    val lexstr : string -> token list
end

structure PCFlexer: PCFLEXER =
struct
  open TextIO

  fun nexttoken strm =
    case input1 strm of
        NONE   => EOF
      | SOME c =>
      if Char.isSpace c then
        nexttoken strm 
      else if Char.isAlpha c then
        let
          fun getid id =
        case lookahead strm of
            NONE   => id
          | SOME d =>
              if Char.isAlpha d orelse Char.isDigit d then
            (input1 strm; getid (id ^ str d))
              else
            id
          val ident = getid (str c)
        in case ident of
           "if"     => IFSYM
         | "then"   => THENSYM
         | "else"   => ELSESYM
         | "bot"    => BOTSYM
         | "true"   => TRUESYM
         | "false"  => FALSESYM
         | "succ"   => SUCCSYM
         | "pred"   => PREDSYM
         | "iszero" => ISZEROSYM
         | "fn"     => FNSYM
         | "rec"    => RECSYM
         | "let"    => LETSYM
         | "in"     => INSYM
         | "end"    => ENDSYM
         | _        => ID ident
        end
      else if Char.isDigit c then
        let
          fun getnum num =
        case lookahead strm of
            NONE   => num
          | SOME d =>
              if Char.isDigit d then
            (input1 strm; getnum (10*num + ord d - ord #"0"))
              else
            num
        in
          NUM (getnum (ord c - ord #"0"))
        end
      else
        case c of
            #"=" => (case lookahead strm of
                 SOME #">" => (input1 strm; FNARROW)
               | _         => EQUAL)
          | #"(" => LPAREN
          | #")" => RPAREN
          | #"|" => VERT
          | #"{" => LBRACE
          | #"}" => RBRACE
          | #"+" => PLUS
          | #"-" => MINUS
          | #"*" => MULT
          | #"/" => DIV
          | #"%" => MOD
          | #"#" =>
          let fun eatline () =
            case input1 strm of
                NONE       => EOF
              | SOME #"\n" => nexttoken strm
              | SOME _     => eatline ()
          in
            eatline ()
          end
          | _  => (print ("Skipping illegal character " ^ str c ^ ".\n");
             nexttoken strm)

  fun gettokens strm =
    let
      fun gettokens_aux toks =
        let val tok = nexttoken strm
        in
      if tok = EOF then
        (closeIn strm; rev (EOF::toks))
          else
        gettokens_aux (tok::toks)
        end
    in
      gettokens_aux []
    end
            
  fun lexstr str = gettokens (openString str)

  fun lexfile file = gettokens (openIn file)

end


signature PCFPARSER =
sig
  val parse : token list -> rc_term
end

structure PCFparser : PCFPARSER =
struct
  fun error msg = print (msg ^ "\n")

  fun parseExp (ID v::tail)      = (LEAF (AST_ID v), tail)
    | parseExp (NUM n::tail)     = (LEAF (AST_NUM n), tail)
    | parseExp (TRUESYM::tail)   = (LEAF (AST_BOOL true), tail)
    | parseExp (FALSESYM::tail)  = (LEAF (AST_BOOL false), tail)
    | parseExp (BOTSYM::tail)    = (LEAF (BOT), tail)
    | parseExp (SUCCSYM::tail)   = (LEAF AST_SUCC, tail)
    | parseExp (PREDSYM::tail)   = (LEAF AST_PRED, tail)
    | parseExp (PLUS::tail)      = (LEAF AST_PLUS, tail)
    | parseExp (MINUS::tail)     = (LEAF AST_MINUS, tail)
    | parseExp (MULT::tail)      = (LEAF AST_MULT, tail)
    | parseExp (DIV::tail)       = (LEAF AST_DIV, tail)
    | parseExp (MOD::tail)       = (LEAF AST_MOD, tail)
    | parseExp (ISZEROSYM::tail) = (LEAF AST_ISZERO, tail)
    | parseExp (IFSYM::tail)     =
    let val (ast1, rest1) = parseExps tail
    in
      if hd rest1 = THENSYM then
        let val (ast2, rest2) = parseExps (tl rest1)
        in
          if hd rest2 = ELSESYM then
        let val (ast3, rest3) = parseExps (tl rest2)
        in
            (AST_IF(ast1, ast2, ast3), rest3)
        end
          else
        (error "Missing else"; 
          (LEAF (AST_ERROR "Missing else"), [EOF]))
        end
      else
        (error "Missing then"; 
          (LEAF (AST_ERROR "Missing then"), [EOF]))
    end
    | parseExp (FNSYM::ID v::FNARROW::tail) =
        let val (ast, rest) = parseExps tail
    in
      (LEAF (AST_FUN(v, ast)), rest)
    end
    | parseExp (FNSYM::ID v::tail) =
    (error ("Missing => after fn " ^ v);
     (LEAF (AST_ERROR ("Missing => after fn " ^ v)), [EOF]))
    | parseExp (FNSYM::tail) =
        (error "Missing identifier after fn"; 
     (LEAF (AST_ERROR "Missing identifier after fn"), [EOF]))
    | parseExp (RECSYM::ID v::FNARROW::tail) =
        let val (ast, rest) = parseExps tail
        in
      (LEAF (AST_REC(v, ast)), rest)
    end
    | parseExp (RECSYM::ID v::tail) =
    (error ("Missing => after rec " ^ v);
     (LEAF (AST_ERROR ("Missing => after rec " ^ v)), [EOF]))
    | parseExp (RECSYM::tail) =
    (error "Missing identifier after rec"; 
     (LEAF (AST_ERROR "Missing identifier after rec"), [EOF]))
    | parseExp (LPAREN::tail) =
        let val (ast, rest) = parseExps tail
    in
      if hd rest = RPAREN then
        (ast, tl rest)
      else
        (error "Missing )"; 
          (LEAF (AST_ERROR "Missing )"), [EOF]))
        end
    | parseExp (LETSYM::ID v::EQUAL::tail) =
    let val (ast1, rest1) = parseExps tail
    in
      if hd rest1 = INSYM then
        let val (ast2, rest2) = parseExps (tl rest1)
        in
          if hd rest2 = ENDSYM then
            (AST_APP (LEAF (AST_FUN(v, ast2)), ast1), tl rest2)
          else
        (error "Missing end"; 
          (LEAF (AST_ERROR "Missing end"), [EOF]))
        end
      else
        (error "Missing in"; 
          (LEAF (AST_ERROR "Missing in"), [EOF]))
    end
    | parseExp (LETSYM::ID v::tail) =
    (error "Missing ="; (LEAF (AST_ERROR "Missing ="), [EOF]))
    | parseExp (LETSYM::tail) =
        (error "Missing identifier after let";
          (LEAF (AST_ERROR "Missing identifier after let"), [EOF]))
    | parseExp (LBRACE::tail) = 
      let val (ast1, rest1) = parseExps tail
    in
        if hd rest1 = VERT then
        let val (ast2, rest2) = parseExps (tl rest1)
        in
            if hd rest2 = RBRACE then
            (NODE (ast1, ast2), tl rest2)
            else
            (error "Missing right brace"; 
              (LEAF (AST_ERROR "Missing right brace"), [EOF]))
        end
        else 
        (error "Missing vert"; 
          (LEAF (AST_ERROR "Missing vert"), [EOF]))
      end
    | parseExp [EOF] = 
        (error "Unexpected EOF"; 
          (LEAF (AST_ERROR "Unexpected EOF"), [EOF]))
    | parseExp _ = 
        (error "Bad expression"; 
          (LEAF (AST_ERROR "Bad expression"), [EOF]))

  and parseExps tokens =
    let
      val (ast, rest) = parseExp tokens

      fun startsExp (ID s)  = true
    | startsExp (NUM n) = true
    | startsExp tok     =
        tok = TRUESYM orelse tok = FALSESYM orelse tok = SUCCSYM orelse
        tok = PREDSYM orelse tok = ISZEROSYM orelse tok = IFSYM orelse
        tok = FNSYM orelse tok = RECSYM orelse tok = LPAREN orelse
        tok = LETSYM orelse tok = LBRACE orelse tok = BOTSYM

  fun parseExps_aux ast rest =
    if startsExp (hd rest) then
      let 
        val (ast', rest') = parseExp rest
      in
        parseExps_aux (AST_APP (ast, ast')) rest'
      end
    else
      (ast, rest)
    in
      parseExps_aux ast rest
    end

  fun lazy parse tokens =
    let val (ast, rest) = parseExps tokens
    in
      if hd rest = EOF then
    ast
      else
    (error "EOF expected"; LEAF (AST_ERROR "EOF expected"))
    end

end

fun parsefile file = PCFparser.parse (PCFlexer.lexfile file)

fun parsestr str = PCFparser.parse (PCFlexer.lexstr str)

