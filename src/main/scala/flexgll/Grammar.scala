package flexgll

import scala.annotation.tailrec

type Grammar[N, T] = Map[N, Set[Rhs[N, T]]]

type Rhs[N, T] = List[Symbol[N, T]]

type Symbol[N, T] = Term[T] | Nt[N]
case class Term[T](t: T)
case class Nt[N](n: N)

type Input[T] = IndexedSeq[T]

type Slot[N, T] = (N, Rhs[N, T], Rhs[N, T])
type Epn[N, T] = (Slot[N, T], Int, Int, Int)
type Epns[N, T] = Set[Epn[N, T]]
type IntsAndEpns[N, T] = (List[Int], Epns[N, T])

type Descr[N, T] = (Slot[N, T], Int, Int)
type Comm[N] = (N, Int)
type Cont[N, T] = (Slot[N, T], Int)

type RList[N, T] = Set[Descr[N, T]] // the set of Rules to be processed
type USet[N, T] = Set[Descr[N, T]]

type GRel[N, T] = Map[Comm[N], Set[Cont[N, T]]]
type PRel[N] = Map[Comm[N], Set[Int]]

def emptyPns[N, T]: Epns[N, T] = Set.empty[Epn[N, T]]
def singlePn[N, T](epn: Epn[N, T]): Epns[N, T] = Set(epn)
def unionPns[N, T](epn1: Epns[N, T], epn2: Epns[N, T]): Epns[N, T] = epn1.union(epn2)
def unionsPns[N, T](epnsList: List[Epns[N, T]]): Epns[N, T] =
  epnsList.foldRight(emptyPns)((epn, acc) => acc.union(epn))

def fromListPns[N, T](epnList: List[Epn[N, T]]): Epns[N, T] =
  epnList.foldRight(emptyPns)((epn, acc) => unionPns(acc, singlePn(epn)))

def popRList[N, T](rList: RList[N, T]): (Descr[N, T], RList[N, T]) = (rList.head, rList.tail)
def emptyRList[N, T]: RList[N, T] = Set.empty
def fromListRList[N, T](ds: RList[N, T], uSet: USet[N, T]): RList[N, T] =
  ds.foldRight(emptyRList[N, T])((d, acc) => if (uSet.contains(d)) acc else acc + d)

def emptyUSet[N, T]: USet[N, T] = Set.empty[Descr[N, T]]
// addDescr d u = u + d
// hasDescr d u = u.contains(d)

def emptyG[N, T] = Map.empty[Comm[N], Set[Cont[N, T]]]

extension[N, T] (gRel: GRel[N, T]) {
  def addCont(comm: Comm[N], cont: Cont[N, T]): GRel[N, T] = {
    val contSet = gRel.getOrElse(comm, Set.empty[Cont[N, T]]) + cont
    gRel.updated(comm, contSet)
  }
  def conts(comm: Comm[N]): Set[Cont[N, T]] = gRel.getOrElse(comm, Set.empty[Cont[N, T]])
}

def emptyP[N] = Map.empty[Comm[N], Set[Int]]

extension[N, T] (pRel: PRel[N]) {
  def addExtent(comm: Comm[N], extent: Int): PRel[N] = {
    val extentSet = pRel.getOrElse(comm, Set.empty[Int]) + extent
    pRel.updated(comm, extentSet)
  }
  def extents(comm: Comm[N]): Set[Int] = pRel.getOrElse(comm, Set.empty[Int])
}

def funrdr[N, T](gram: Grammar[N, T], x: Nt[N], inp: Input[T]): Boolean = {
  // bounds(inp) = (0, inp.length)
  val matches = descend1(gram, inp, x, 0)
  matches.contains(inp.length)
}

def funrdp[N, T](gram: Grammar[N, T], x: Nt[N], inp: Input[T]): Epns[N, T] =
  descend2(gram, inp, x, 0)._2

def fungll[N, T](gram: Grammar[N, T], x: Nt[N], inp: Input[T]) = {
  val R = fromListRList(descend(gram, x, 0), emptyUSet)
  loop(gram, inp, R, emptyUSet, emptyG, emptyP, emptyPns)
}

@tailrec
def loop[N, T](
    gram: Grammar[N, T], inp: Input[T],
    rList: RList[N, T], uSet: USet[N, T],
    gRel: GRel[N, T], pRel: PRel[N], epns: Epns[N, T]
): (USet[N, T], Epns[N, T]) = if (rList.isEmpty) {
  (uSet, epns)
} else {
  val (d, rPrime) = popRList(rList)
  val ((rlist, nsPrime), mcont, mpop) = process(gram, inp, d, gRel, pRel)
  val uPrime = uSet + d
  val rDoublePrime = rPrime.union(fromListRList(rlist, uPrime))
  val gPrime = mcont match {
    case Some(k, v) => gRel.addCont(k, v)
    case _ => gRel
  }
  val pPrime = mpop match {
    case Some(k, v) => pRel.addExtent(k, v)
    case _ => pRel
  }

  loop(gram, inp, rDoublePrime, uPrime, gPrime, pPrime, epns.union(nsPrime))
}

def descend1[N, T](gram: Grammar[N, T], inp: Input[T], x: Nt[N], leftExtent: Int): List[Int] = {
  val alts = gram.get(x.n).map(_.toList).getOrElse(Nil)
  alts.flatMap(beta => process1(gram, inp, beta, leftExtent))
}

def descend2[N, T](gram: Grammar[N, T], inp: Input[T], x: Nt[N], l: Int) = {
  val alts = gram.get(x.n).map(_.toList).getOrElse(Nil)
  concat2(alts.map(rhs => processInit(gram, inp, x, l, rhs)))
}

def descend[N, T](gram: Grammar[N, T], x: Nt[N], k: Int): RList[N, T] = {
  val alts = gram.get(x.n).getOrElse(Set.empty)
  alts.map(beta => ((x.n, Nil, beta), k, k))
}

def concat2[N, T](ies: List[IntsAndEpns[N, T]]): IntsAndEpns[N, T] = {
  def combine[N, T](ies1: IntsAndEpns[N, T], ies2: IntsAndEpns[N, T]): IntsAndEpns[N, T] =
    (ies1._1 ++ ies2._1, unionPns(ies1._2, ies2._2))

  ies.foldRight((List.empty[Int], emptyPns))((ie, acc) => combine(ie, acc))
}

def process1[N, T](gram: Grammar[N, T], inp: Input[T], beta: Rhs[N, T], k: Int): List[Int] =
  beta match {
    case Nil => List(k)
    case w :: betaPrime =>
      val ks: List[Int] = w match {
        case x: Nt[N] => descend1(gram, inp, x, k)
        case t: Term[T] if matches1(inp, t, k) => List(k + 1)
        case _ => List.empty
      }
      ks.flatMap(kPrime => process1(gram, inp, betaPrime, kPrime))
  }

def processInit[N, T](
    gram: Grammar[N, T],
    inp: Input[T],
    x: Nt[N],
    leftExtent: Int,
    beta: Rhs[N, T]
): IntsAndEpns[N, T] = process2(gram, inp, (x.n, Nil, beta), leftExtent, leftExtent)

def process2[N, T](
    gram: Grammar[N, T],
    inp: Input[T],
    slot: Slot[N, T],
    l: Int,
    k: Int
): IntsAndEpns[N, T] = {
  val (x, alpha, beta) = slot
  beta match {
    case Nil if alpha == Nil => (List(k), singlePn((x, Nil, Nil), l, l, l))
    case Nil => (List(k), emptyPns)
    case w :: betaPrime =>
      def continue(slot: Slot[N, T], ksAndEpns: IntsAndEpns[N, T]): IntsAndEpns[N, T] = {
        val (rs, ns) = ksAndEpns
        val (rsPrime, nsPrime): IntsAndEpns[N, T] = concat2(
          rs.map(r => process2(gram, inp, slot, l, r)))
        val nsDoublePrime = fromListPns(rs.map(r => (slot, l, k, r)))
        (rsPrime, unionsPns(List(ns, nsPrime, nsDoublePrime)))
      }

      val ksAndEpns: IntsAndEpns[N, T] = w match {
        case n: Nt[N] => descend2(gram, inp, n, k)
        case t: Term[T] if matches1(inp, t, k) => (List(k + 1), emptyPns)
        case _ => (Nil, emptyPns)
      }
      continue((x, alpha :+ w, betaPrime), ksAndEpns)
  }
}

def process[N, T](
    gram: Grammar[N, T],
    inp: Input[T],
    d: Descr[N, T],
    gRel: GRel[N, T],
    pRel: PRel[N]
): ((RList[N, T], Epns[N, T]), Option[(Comm[N], Cont[N, T])], Option[(Comm[N], Int)]) = {
  val (slot, l, k) = d
  val (x, alpha, beta) = slot
  beta match {
    case Nil =>
      val K: Set[Cont[N, T]] = gRel.conts((x, l))
      val (rlist: RList[N, T], ns) = ascend(l, K, k)
      val nsPrime = alpha match {
        case Nil => singlePn((x, Nil, Nil), l, k, k)
        case _ => emptyPns[N, T]
      }
      ((rlist, unionPns(ns, nsPrime)), None, Some((x, l), k))
    case w :: betaPrime => w match {
      case t: Term[T] => (matches(inp, (x, alpha, beta), l, k), None, None)
      case y: Nt[N] =>
        val R = pRel.extents(y.n, k)
        val cc: (Comm[N], Cont[N, T]) = ((y.n, k), ((x, alpha :+ w, betaPrime), l))
        if (R.isEmpty) {
          ((descend(gram, y, k), emptyPns), Some(cc), None)
        } else {
          (skip(k, ((x, alpha :+ w, betaPrime), l), R), Some(cc), None)
        }
    }
  }
}

def skip[N, T](k: Int, d: Cont[N, T], R: Set[Int]) = nmatch(k, Set(d), R)

def ascend[N, T](k: Int, K: Set[Cont[N, T]], r: Int) = nmatch(k, K, Set(r))

def nmatch[N, T](k: Int, ks: Set[Cont[N, T]], rs: Set[Int]): (RList[N, T], Epns[N, T]) = {
  val rlist = for {
    r <- rs
    (slot, l) <- ks
  } yield {
    (slot, l, r)
  }

  val elist = rlist.map { case (slot, l, r) => (slot, l, k, r) }
  (rlist, elist)
}


def matches1[T](inp: Input[T], t: T, index: Int): Boolean =
  index >= 0 && index < inp.length && inp(index) == t

def matches[N, T](inp: Input[T], slot: Slot[N, T], l: Int, k: Int): (RList[N, T], Epns[N, T]) = {
  val (x, alpha, w :: beta) = slot
  w match {
    case t: Term[T] =>
      if (matches1(inp, t, k)) {
        (Set(((x, alpha :+ t, beta), l, k + 1)), singlePn((x, alpha :+ t, beta), l, k, k + 1))
      } else {
        (Set.empty, emptyPns)
      }
    case _ => throw RuntimeException(
      "Can't call matches unless the part after the dot is a terminal")
  }
}

/* Examples */

val TupleG: Grammar[String, Char] = Map(
  "tuple" -> Set(List(Term('('), Nt("as"), Term(')'))),
  "as" -> Set(
    List(),
    List(Term('a'), Nt("more"))),
  "more" -> Set(
    List(),
    List(Term(','), Term('a'), Nt("more"))
  )
)

val TripleE: Grammar[String, Char] = Map(
  "E" -> Set(
    List(Nt("E"), Nt("E"), Nt("E")),
    List(Term('1')),
    List()
  ),
)

@main
def main(): Unit = {
  fungll(TripleE, Nt("E"), "1")._2.toList.sortBy(t => (t._2, t._3, t._4)).foreach {
    println(_)
  }
}
