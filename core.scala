// Import dependancies
import scala.language.implicitConversions    
import scala.language.reflectiveCalls

// REGEX: Definitions
abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class RANGE(s: Set[Char]) extends Rexp 
case class CFUN(f: Char => Boolean) extends Rexp

/* VALUES: Definitions */
abstract class Val
case object Empty extends Val
case object Optional extends Val
case class Chr(c: Char) extends Val
case class Rge(s: Set[Char]) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Plus(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val

/* Coding convenience: "String" to SEQ(...)/CHAR(...) */
def list_to_regex(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), list_to_regex(s))
}
implicit def string_to_regex(s : String) : Rexp = 
  list_to_regex(s.toList)

/* Coding convenience: "|" | "%" | "~" to ALT, STAR, SEQ */
implicit def op_to_regex(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

/* Coding convenience: "|" | "%" | "~" to ALT, STAR, SEQ */
implicit def string_ops_to_regex(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

// TRUE if REGEX r can match empty string.
def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case PLUS(r) => nullable(r)
  case OPTIONAL(r) => true
  case RANGE(s) => false
  case CFUN(f) => false
  case RECD(_, r1) => nullable(r1)
}

// Returns REGEX with character c taken off strings in L(r)
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
  case PLUS(r) => SEQ(der(c, r), STAR(r)) 
  case OPTIONAL(r) => ALT(ONE, der(c, r)) 
  case RANGE(s) => if (s.contains(c)) ONE else ZERO
  case CFUN(f) => if (f(c)) ONE else ZERO 
}

/* MKEPS: Return part of regular expression matching empty string */
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case PLUS(r) => Plus(Nil)
  case OPTIONAL(r) => Optional
  case RECD(x, r) => Rec(x, mkeps(r))
}

/* INJECTION: Return Value of Regular Expression w.r.t character c */
def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RANGE(s), Empty) => Rge(Set(c))
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}

// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}


// extracts an environment from a value;
// used for tokenise a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}


// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = 
  env(lex_simp(r, s.toList))



/* MKEPS: Tests */
mkeps(ONE | RANGE(Set('a', 'b'))) // Left(Empty)
mkeps(RANGE(Set('a', 'b')) | ONE) // Right(Empty)
mkeps(PLUS("ajhghj"))


// REGEX: Syntactic Entities
            val SYM         = RANGE(('A' to 'Z').toSet ++ ('a' to 'z').toSet ++ Set('_'))
            val DIGIT       = RANGE(('0' to '9').toSet)
/* Q1.1 */  val KEYWORD     : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "read" | "write" | "skip"
/* Q1.2 */  val OP          : Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | ":=" | "&&" | "||"
/* Q1.3 */  val STRING      : Rexp = "\"" ~ SYM.% ~ "\""
/* Q1.4 */  val OCPARAN     : Rexp = "{" // OCPAREN = Opening Curly Parentheses
            val CCPAREN     : Rexp = "}" // CCPAREN = Closing Curly Parentheses
            val OPAREN      : Rexp = "(" // OPAREN  = Opening Parentheses
            val CPAREN      : Rexp = ")" // CPAREN  = Closing Parentheses
/* Q1.5 */  val SEMI        : Rexp = ";"
/* Q1.6 */  val WHITESPACE  = PLUS(" " | "\n" | "\t")
/* Q1.7 */  val ID          = SYM ~ (SYM | DIGIT).% 
/* Q1.8 */  val NLZEROES    = "0" | (RANGE(('1' to '9').toSet) ~ (DIGIT.%)) // NLZEROES = No Leading Zeroes


val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NLZEROES) | 
                  ("s" $ SEMI) | 
                  ("str" $ STRING) |
                  ("p" $ (OPAREN | CPAREN)) | 
                  ("pc" $ (OCPARAN | CCPAREN)) |
                  ("w" $ WHITESPACE)).%


