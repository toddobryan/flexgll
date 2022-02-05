package flexgll

import scala.annotation.targetName

type Parser[T, A] = (Input[T], Int) => Set[(Int, A)]

extension [T, A] (p: Parser[T, A]) {
  @targetName("or")
  def |(q: Parser[T, A]): Parser[T, A] = (inp: Input[T], k: Int) => {
    p(inp, k) ++ q(inp, k)
  }
}

extension [T, A, B] (p: Parser[T, A => B]) {
  @targetName("cat")
  def ~(q: Parser[T, A]): Parser[T, B] = (inp: Input[T], l: Int) => {
    for {
      (k, f) <- p(inp, l)
      (r, a) <- q(inp, k)
    } yield {
      (r, f(a))
    }
  }
}

def runParser[T, A](p: Parser[T, A], inp: Input[T]): Set[A] = for {
  (r, a) <- p(inp, 0) if r == inp.length + 1
} yield {
  a
}

def term1[T](t: T): Parser[T, T] = (inp: Input[T], k: Int) =>
    if matches1(inp, t, k) then Set((k + 1, inp(k))) else Set.empty

def succeeds[T, A](v: A): Parser[T, A] = (inp: Input[T], k: Int) =>
    Set((k, v))

def fails[T, A]: Parser[T, A] = (inp: Input[T], k: Int) => Set.empty

type GrammarGen[N, T] = ((Set[N], Grammar[N, T])) => (Set[N], Grammar[N, T])

type SymbG[N, T] = (Symbol[N, T], GrammarGen[N, T])
type SeqG[N, T] = (Rhs[N, T], GrammarGen[N, T])
type ChoiceG[N, T] = (List[Rhs[N, T]], GrammarGen[N, T])

def grammarOf[N, T](start: Nt[N], symbG: SymbG[N, T]): Grammar[N, T] = {
  val (n, pgen) = symbG
  val gram: Grammar[N, T] = Map(start.n -> Set(List(n)))
  pgen(Set.empty, gram)._2
}

def termGr[T](t: T) = (Term(t), identity)

def ntermGr[N, T](n: N, p: ChoiceG[N, T]): SymbG[N, T] = {
  val (alts, pgen) = p
  def gen(nts: Set[N], gram: Grammar[N, T]): (Set[N], Grammar[N, T]) = {
    if (nts.contains(n)) {
      (nts, gram)
    } else {
      val ntsPrime = nts + n
      val gramPrime = gram.insertWith(
        (newNts: Set[Rhs[N, T]], oldNts: Set[Rhs[N, T]]) => newNts.union(oldNts),
        n,
        alts.toSet
      )
      pgen(ntsPrime, gramPrime)
    }
  }

  (Nt(n), gen(_, _))
}

extension [K, V] (map: Map[K, V]) {
  private def insertWith(f: (V, V) => V, key: K, value: V): Map[K, V] =
    if (map.contains(key)) {
      map + (key -> f(value, map(key)))
    } else {
      map + (key -> value)
    }
}

def altStartGr[N, T]: ChoiceG[N, T] = (Nil, identity)

def altGr[N, T](choice: ChoiceG[N, T], seq: SeqG[N, T]): ChoiceG[N, T] = {
  val (as, pgen) = choice
  val (alpha, qgen) = seq
  (as ++ Set(alpha), qgen.compose(pgen))
}

def seqStartGr[N, T]: SeqG[N, T] = (Nil, identity)

def seqGr[N, T](seq: SeqG[N, T], symb: SymbG[N, T]): SeqG[N, T] = {
  val (alpha, pgen) = seq
  val (s, qgen) = symb
  (alpha :+ s, pgen.compose(qgen))
}

def parserFor[N, T](start: Nt[N], p: SymbG[N, T], inp: Input[T]): Epns[N, T] =
  fungll(grammarOf(start, p), start, inp)._2

type OracleParser[N, T, A] = (Epns[N, T], Int, Int, Set[N]) => List[A]

type SymbS[N, T, A] = (Symbol[N, T], OracleParser[N, T, A])
type SeqS[N, T, A] = (Rhs[N, T], (N,  Rhs[N, T]) => OracleParser[N, T, A])
type ChoiceS[N, T, A] = N => OracleParser[N, T, A]

def termSem[N, T](t: T): SymbS[N, T, T] = {
  def gen(ns: Epns[N, T], l: Int, r: Int, nts: Set[N]): List[T] =
    if (r == l + 1) List(t) else Nil

  (Term(t), gen)
}

def ntermSem[N, T, A](x: N, p: ChoiceS[N, T, A]): SymbS[N, T, A] = {
  def gen(ns: Epns[N, T], l: Int, r: Int, nts: Set[N]): List[A] = {
    if (nts.contains(x)) Nil else p(x)(ns, l, r, nts + x)
  }

  (Nt(x), gen)
}

def altStartSem[N, T, A]: ChoiceS[N, T, A] =
  (x: N) => (ns: Epns[N, T], l: Int, r: Int, nts: Set[N]) => Nil

def altSem[N, T, A](p: ChoiceS[N, T, A], seqS: SeqS[N, T, A]): ChoiceS[N, T, A] = {
  val (alpha, q) = seqS
  (x: N) => (ns: Epns[N, T], l: Int, r: Int, nts: Set[N]) =>
      p(x)(ns, l, r, nts) ++ q(x, Nil)(ns, l, r, nts)
}

def seqStartSem[N, T, A](a: A): SeqS[N, T, A] = {
  def gen(x: N, beta: Rhs[N, T]): OracleParser[N, T, A] =
    (ns: Epns[N, T], l: Int, r: Int, nts: Set[N]) => if (l == r) List(a) else Nil

  (Nil, gen)
}

def seqSem[N, T, A, B](seq: SeqS[N, T, A => B], symbS: SymbS[N, T, A]): SeqS[N, T, B] = {
  val (alpha, p) = seq
  val (s, q) = symbS

  def leftLabels(nts: Set[N], l: Int, k: Int, r: Int): Set[N] = if (k < r) Set.empty else nts
  def rightLabels(nts: Set[N], l: Int, k: Int, r: Int): Set[N] = if (k > l) Set.empty else nts
  def gen(x: N, beta: Rhs[N, T]): OracleParser[N, T, B] =
    (ns: Epns[N, T], l: Int, r: Int, nts: Set[N]) => for {
      k <- pivots(((x, alpha :+ s, beta), l, r), ns).toList
      f <- p(x, s :: beta)(ns, l, k, leftLabels(nts, l, k, r))
      a <- q(ns, k, r, rightLabels(nts, l, k, r))
    } yield {
      f(a)
    }

  (alpha :+ s, gen)
}

def pivots[N, T](descr: Descr[N, T], ns: Epns[N, T]): Set[Int] = {
  val (slot, l, r) = descr
  for {
    (slotPrime, lPrime, pivot, rPrime) <- ns if slot == slotPrime && l == lPrime && r == rPrime
  } yield {
    pivot
  }
}

def evaluatorFor[N, T, A](symbS: SymbS[N, T, A], l: Int, r: Int, ns: Epns[N, T]): List[A] = {
  val (_, p) = symbS
  p(ns, l, r, Set.empty)
}
