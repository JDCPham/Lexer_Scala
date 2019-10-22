/* 
 * Author: John Pham
 * Written: 8 October 2019
 * Institution: King's College London
 * Course: Compilers & Formal Languages
*/

/* Constructors */
abstract class Rexp
case object ZERO extends Rexp          
case object ONE extends Rexp                   
case class CHAR(c: Char) extends Rexp          
case class ALT(r1: Rexp, r2: Rexp) extends Rexp  
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp  
case class STAR(r: Rexp) extends Rexp     
case class RANGE(s: Set[Char]) extends Rexp 
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp
case class UPTO(r: Rexp, m: Int) extends Rexp
case class FROM(r: Rexp, n: Int) extends Rexp
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class NOT(r: Rexp) extends Rexp 
case class CFUN(f: Char => Boolean) extends Rexp

/* True if empty string matches regex r */
def nullable(r: Rexp) : Boolean = r match {
  case ZERO             => false
  case ONE              => true
  case CHAR(_)          => false
  case ALT(r1, r2)      => nullable(r1) || nullable(r2)
  case SEQ(r1, r2)      => nullable(r1) && nullable(r2)
  case STAR(_)          => true
  case RANGE(s)         => false
  case PLUS(r)          => nullable(r)
  case OPTIONAL(r)      => true
  case NTIMES(r, i)     => if (i == 0) true else nullable(r)
  case UPTO(r, _)       => true
  case FROM(r, i)       => if (i == 0) true else nullable(r)
  case BETWEEN(r, i, _) => if (i == 0) true else nullable(r)
  case NOT(r)           => !nullable(r)
  case CFUN(f)          => false
}

/* Derivative of a regex r w.r.t c */
def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO             => ZERO
  case ONE              => ZERO
  case CHAR(d)          => if (c == d) ONE else ZERO
  case ALT(r1, r2)      => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2)      => if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2)) else SEQ(der(c, r1), r2)
  case STAR(r1)         => SEQ(der(c, r1), STAR(r1))
  case RANGE(s)         => if (s.contains(c)) ONE else ZERO
  case PLUS(r)          => SEQ(der(c, r), STAR(r)) // Ok
  case OPTIONAL(r)      => ALT(ZERO, der(c, r))
  case NTIMES(r, i)     => if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))  //Ok
  case UPTO(r, i)       => if (i == 0) ZERO else SEQ(der(c, r), UPTO(r, i - 1)) //Ok
  case FROM(r, i)       => if (i == 0) SEQ(der(c, r), FROM(r, i)) else SEQ(der(c, r), FROM(r, i - 1))
  case BETWEEN(r, i, j) => if (i == 0) SEQ(der(c, r), UPTO(r, j - 1)) else SEQ(der(c, r), BETWEEN(r, i - 1, j - 1))
  case NOT(r)           => NOT(der(c, r))
  case CFUN(f)          => if (f(c)) ONE else ZERO // OK
}



/* Simplifies expressions where possible */
def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}

/* Derivative w.r.t characters in string s */
def ders (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => {
    ders(s, simp(der(c, r)));

  }
}

/* True if string s matches regex r */
def matcher(r: Rexp, s: String) : Boolean = nullable(ders(s.toList, r))

/* Functions for CFUN */
def CHAR(c: Char) = CFUN(_ == c);
def RANGE(cs: Set[Char]) = CFUN(cs.contains(_))
def ALL = CFUN((c: Char) => true)


/* Function for CFUN (Returns true when c is [a-z0-9_.-]) */
def email1(c: Char) : Boolean = {
  if (('a' to 'z').toList.contains(c)) return true;
  if (('0' to '9').toList.contains(c)) return true;
  if (List('_', '.', '-').contains(c)) return true;
  return false;
}

/* Function for CFUN (Returns true when c is [a-z.]) */
def email2(c: Char) : Boolean = {
  if (('a' to 'z').toList.contains(c)) return true;
  if (List('.').contains(c)) return true;
  return false;
}

val emailSet1 = ('a' to 'z').toSet union ('0' to '9').toSet union Set('.', '_', '-')
val emailSet2 = ('a' to 'z').toSet union Set('.')

/* Email Address Regular Expression */
val emailRegex = SEQ(PLUS(CFUN(email1)), SEQ(CHAR('@'), SEQ(PLUS(CFUN(email1)), SEQ(CHAR('.'), BETWEEN(CFUN(email2), 2, 6)))));
val emailRegex2 = SEQ(PLUS(RANGE(emailSet1)), SEQ(CHAR('@'), SEQ(PLUS(RANGE(emailSet1)), SEQ(CHAR('.'), BETWEEN(RANGE(emailSet2), 2, 6)))));
simp(ders("john.pham@kcl.ac.uk".toList, emailRegex))
ders("john.pham@kcl.ac.uk".toList, emailRegex2)


/* Nullable Test Cases */
nullable(ZERO) == false                                       // nullable() = false
nullable(ONE) == true                                         // nullable([]) = true 
nullable(CHAR('a')) == false                                  // nullable(a) = false
nullable(ALT(CHAR('a'), CHAR('b'))) == false                  // nullable(a + b) = false
nullable(ALT(ONE, CHAR('a'))) == true                         // nullable([] + a) = true
nullable(ALT(ZERO, CHAR('b'))) == false                       // nullable( + b) = false
nullable(ALT(SEQ(CHAR('a'), CHAR('b')), CHAR('a'))) == false  // nullable((ab) + a) = false
nullable(ALT(ALT(CHAR('a'), ONE), CHAR('a'))) == true         // nullable((a + []) + a) = true
nullable(STAR(CHAR('a'))) == true                             // nullable(a*) = true
nullable(STAR(SEQ(CHAR('a'), CHAR('b')))) == true             // nullable((ab)*) = true
nullable(RANGE(Set('a', 'b', 'c', 'd'))) == false             // nullable([a, b, c, d]) = false
nullable(RANGE(Set('a'))) == false                            // nullable([a]) = false
nullable(OPTIONAL(CHAR('a'))) == true                         // nullable(a?) = true
nullable(CFUN(a)) == false                                    // nullable(a) = false


/* Tests as given in Coursework Handout */
matcher(NTIMES(CHAR('a'), 3), "") == false
matcher(NTIMES(CHAR('a'), 3), "a") == false
matcher(NTIMES(CHAR('a'), 3), "aa") == false
matcher(NTIMES(CHAR('a'), 3), "aaa") == true
matcher(NTIMES(CHAR('a'), 3), "aaaa") == false
matcher(NTIMES(CHAR('a'), 3), "aaaaa") == false

matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "") == true
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "a") == true
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "aa") == true
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "aaa") == true 
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "aaaa") == false
matcher(NTIMES(OPTIONAL(CHAR('a')), 3), "aaaaa") == false

matcher(UPTO(CHAR('a'), 3), "") == true
matcher(UPTO(CHAR('a'), 3), "a") == true
matcher(UPTO(CHAR('a'), 3), "aa") == true
matcher(UPTO(CHAR('a'), 3), "aaa") == true
matcher(UPTO(CHAR('a'), 3), "aaaa") == false
matcher(UPTO(CHAR('a'), 3), "aaaaa") == false

matcher(UPTO(OPTIONAL(CHAR('a')), 3), "") == true
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "a") == true
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "aa") == true
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "aaa") == true
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "aaaa") == false
matcher(UPTO(OPTIONAL(CHAR('a')), 3), "aaaaa") == false

matcher(BETWEEN(CHAR('a'), 3, 5), "") == false
matcher(BETWEEN(CHAR('a'), 3, 5), "a") == false
matcher(BETWEEN(CHAR('a'), 3, 5), "aa") == false
matcher(BETWEEN(CHAR('a'), 3, 5), "aaa") == true
matcher(BETWEEN(CHAR('a'), 3, 5), "aaaa") == true
matcher(BETWEEN(CHAR('a'), 3, 5), "aaaaa") == true

matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "a") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "aa") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "aaa") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "aaaa") == true
matcher(BETWEEN(OPTIONAL(CHAR('a')), 3, 5), "aaaaa") == true





/* Question 7 */
val r1regex = SEQ(SEQ(CHAR('a'), CHAR('a')), CHAR('a'));
val r2regex = SEQ(NTIMES(CHAR('a'), 19), ALT(ONE, CHAR('a')));

val r3regex = PLUS(PLUS(r1regex));
val r4regex = PLUS(PLUS(r2regex));

// 5
matcher(r3regex, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
matcher(r4regex, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");

// 6
matcher(r3regex, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
matcher(r4regex, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");

// 7
matcher(r3regex, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
matcher(r4regex, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");