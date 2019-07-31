// Associativity of matrix multiplication

type Pos = x | 0 < x witness 1
const N : Pos
type Index = x | 0 <= x < N

type Matrix = Index -> Index -> int

// We assume functional extensionality as an axiom
lemma FunEq<X, Y>(f: X -> Y, g: X -> Y)
    requires forall x :: f(x) == g(x) 
    ensures f == g 
{ assume false; }

lemma Same(m1: Matrix, m2: Matrix)
    requires forall x, y :: m1(x)(y) == m2(x)(y)
    ensures m1 == m2
{
    forall x ensures m1(x) == m2(x) {
        FunEq(m1(x), m2(x));
    }
    FunEq(m1, m2);
}

function method Sum_n(f: Index -> int, n: nat): int
    requires n <= N
{
    if n == 0 then 0 else f(n - 1) + Sum_n(f, n - 1)
}

function method Sum(f: Index -> int): int {
    Sum_n(f, N)
}

function method mult(m1: Matrix, m2: Matrix): Matrix
{
    ((x: Index) => (y: Index) =>
        Sum((k: Index) => m1(x)(k) * m2(k)(y)))
}

lemma distr_add_n(f: Index -> int, g: Index -> int, n: nat)
    requires n <= N
    ensures Sum_n(f, n) + Sum_n(g, n) == Sum_n((i: Index) => f(i) + g(i), n)    // Sum(f) + Sum(g) == Sum(f0(f, g))      f0(l0, l1)[x] == l0(x) + l1(x)
{}

lemma distr_mult_n(f: Index -> int, n: nat, x: int) 
    requires n <= N
    ensures Sum_n(f, n) * x == Sum_n((i: Index) => f(i) * x, n)
{}

lemma distr_mult(f: Index -> int, x: int) 
    ensures Sum(f) * x == Sum((i: Index) => f(i) * x)
{
    distr_mult_n(f, N, x);
}

lemma sum_assoc_n(m: Matrix, n1: nat, n2: nat)
    requires n1 <= N && n2 <= N
    ensures Sum_n((k: Index) => Sum_n((l: Index) => m(k)(l), n1), n2) == Sum_n((l: Index) => Sum_n((k: Index) => m(k)(l), n2), n1)
    {
        var f  := (k: Index) => Sum_n((l: Index) => m(k)(l), n1);
        var g  := (l: Index) => Sum_n((k: Index) => m(k)(l), n2);
        if (n2 == 0) {
            calc {
                Sum_n(f, n2);
                ==
                0;
                ==
                Sum_n(g, n2);
            }
        } else {
            var f2 := (l: Index) => m(n2 - 1)(l);
            var g2 := (l: Index) => Sum_n((k: Index) => m(k)(l), n2 - 1);
            calc {
                Sum_n(f, n2);
                == // def of Sum_n
                f(n2 - 1) + Sum_n(f, n2 - 1);
                == // beta reduction
                Sum_n(f2, n1) + Sum_n(f, n2 - 1);
                == // IH applied to Sum_n(f, n2 - 1)
                Sum_n(f2, n1) + Sum_n(g2, n1);
                == { distr_add_n(f2, g2, n1); }
                Sum_n((l: Index) => f2(l) + g2(l), n1);
                == { // substituting f2 and g2
                     FunEq((l: Index) => f2(l) + g2(l), (l: Index) => m(n2 - 1)(l) + Sum_n((k: Index) => m(k)(l), n2 - 1)); 
                   }
                Sum_n((l: Index) => m(n2 - 1)(l) + Sum_n((k: Index) => m(k)(l), n2 - 1), n1);
                == { FunEq((l: Index) => m(n2 - 1)(l) + Sum_n((k: Index) => m(k)(l), n2 - 1), (l: Index) => Sum_n((k: Index) => m(k)(l), n2)); }
                Sum_n((l: Index) => Sum_n((k: Index) => m(k)(l), n2), n1);
            }
        }
    }

lemma sum_assoc(m: Matrix)
    ensures Sum((k: Index) => Sum((l: Index) => m(k)(l))) == Sum((l: Index) => Sum((k: Index) => m(k)(l)))
    {
        calc {
            Sum((k: Index) => Sum((l: Index) => m(k)(l)));
            == { FunEq((k: Index) => Sum((l: Index) => m(k)(l)), (k: Index) => Sum_n((l: Index) => m(k)(l), N)); }
            Sum_n((k: Index) => Sum_n((l: Index) => m(k)(l), N), N);
            == { sum_assoc_n(m, N, N); }
            Sum_n((l: Index) => Sum_n((k: Index) => m(k)(l), N), N);
            == { FunEq((l: Index) => Sum((k: Index) => m(k)(l)), (l: Index) => Sum_n((k: Index) => m(k)(l), N)); }
            Sum((l: Index) => Sum((k: Index) => m(k)(l)));
        }
    }

lemma sum_assoc_mult(m1: Matrix, m2: Matrix, m3: Matrix, i: Index, j: Index) 
    ensures Sum((k: Index) => Sum((l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j))) == Sum((l: Index) => Sum((k: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)))
    {
        var m := (k1: Index) => (l1: Index) => m1(i)(l1) * m2(l1)(k1) * m3(k1)(j);
        calc {
            Sum((k: Index) => Sum((l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)));
            == { 
                forall k: Index
                    ensures ((l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)) == ((l: Index) => m(k)(l))
                    {
                        FunEq((l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j), (l: Index) => m(k)(l));
                    }
                FunEq((k: Index) => Sum((l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)), (k: Index) => Sum((l: Index) => m(k)(l)));
               }
            Sum((k: Index) => Sum((l: Index) => m(k)(l)));
            == { sum_assoc(m); }
            Sum((l: Index) => Sum((k: Index) => m(k)(l)));
            == {
                forall l: Index
                    ensures ((k: Index) => m(k)(l)) == ((k: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j))
                    {
                        FunEq((k: Index) => m(k)(l), 
                              (k: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j));
                    }
                    FunEq((l: Index) => Sum((k: Index) => m(k)(l)), (l: Index) => Sum((k: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)));
               }
            Sum((l: Index) => Sum((k: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)));
        }
    }

lemma mult_assoc_ij(m1: Matrix, m2: Matrix, m3: Matrix, i: Index, j: Index)
    ensures mult(mult(m1, m2), m3)(i)(j) == mult(m1, mult(m2, m3))(i)(j)
{
    calc {
        mult(mult(m1, m2), m3)(i)(j);
        ==
        Sum((k: Index) => mult(m1, m2)(i)(k) * m3(k)(j));
        == { 
            assert forall k : Index :: mult(m1, m2)(i)(k) == Sum((l: Index) => m1(i)(l) * m2(l)(k)); 
            FunEq((k: Index) => mult(m1, m2)(i)(k) * m3(k)(j), (k: Index) => Sum((l: Index) => m1(i)(l) * m2(l)(k)) * m3(k)(j));
           }
        Sum((k: Index) => Sum((l: Index) => m1(i)(l) * m2(l)(k)) * m3(k)(j));
        == { 
            forall k: Index 
                ensures Sum((l: Index) => m1(i)(l) * m2(l)(k)) * m3(k)(j) == Sum((l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j))
              {
                var g := (l: Index) => m1(i)(l) * m2(l)(k);
                var x := m3(k)(j);
                calc {
                    Sum((l: Index) => m1(i)(l) * m2(l)(k)) * m3(k)(j);
                    ==
                    Sum(g) * x;
                    == { distr_mult(g, x); }
                    Sum((l: Index) => g(l) * x);
                    == { FunEq((l: Index) => g(l) * x, (l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)); }
                    Sum((l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j));
                }
            }
            FunEq((k: Index) => Sum((l: Index) => m1(i)(l) * m2(l)(k)) * m3(k)(j), (k: Index) => Sum((l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)));
           }
                Sum((k: Index) => Sum((l: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)));
                == { sum_assoc_mult(m1, m2, m3, i, j); }
                Sum((l: Index) => Sum((k: Index) => m1(i)(l) * m2(l)(k) * m3(k)(j)));
        == // alpha-renaming k <-> l
        Sum((k: Index) => Sum((l: Index) => m1(i)(k) * m2(k)(l) * m3(l)(j)));
        == {
            forall k: Index 
                ensures Sum((l: Index) => m1(i)(k) * m2(k)(l) * m3(l)(j)) == Sum((l: Index) => m2(k)(l) * m3(l)(j) * m1(i)(k))
            {
                FunEq((l: Index) => m1(i)(k) * m2(k)(l) * m3(l)(j), (l: Index) => m2(k)(l) * m3(l)(j) * m1(i)(k));
            }
            FunEq((k: Index) => Sum((l: Index) => m1(i)(k) * m2(k)(l) * m3(l)(j)), (k: Index) => Sum((l: Index) => m2(k)(l) * m3(l)(j) * m1(i)(k)));
           }
        Sum((k: Index) => Sum((l: Index) => m2(k)(l) * m3(l)(j) * m1(i)(k)));
        == {
            forall k: Index
                ensures Sum((l: Index) => m2(k)(l) * m3(l)(j)) * m1(i)(k) == Sum((l: Index) => m2(k)(l) * m3(l)(j) * m1(i)(k));
            {
                var g := (l: Index) => m2(k)(l) * m3(l)(j);
                var x := m1(i)(k);
                calc {
                    Sum((l: Index) => m2(k)(l) * m3(l)(j)) * m1(i)(k);
                    ==
                    Sum(g) * x;
                    == { distr_mult(g, x); }
                    Sum((l: Index) => g(l) * x);
                    == { FunEq((l: Index) => g(l) * x, (l: Index) => m2(k)(l) * m3(l)(j) * m1(i)(k)); }
                    Sum((l: Index) => m2(k)(l) * m3(l)(j) * m1(i)(k));
                }
            }
            FunEq((k: Index) => Sum((l: Index) => m2(k)(l) * m3(l)(j) * m1(i)(k)), (k: Index) => Sum((l: Index) => m2(k)(l) * m3(l)(j)) * m1(i)(k));
           }
        Sum((k: Index) => Sum((l: Index) => m2(k)(l) * m3(l)(j)) * m1(i)(k));
        == { FunEq((k: Index) => Sum((l: Index) => m2(k)(l) * m3(l)(j)) * m1(i)(k), (k: Index) => m1(i)(k) * Sum((l: Index) => m2(k)(l) * m3(l)(j))); }
        Sum((k: Index) => m1(i)(k) * Sum((l: Index) => m2(k)(l) * m3(l)(j)));
        == { FunEq((k: Index) => m1(i)(k) * Sum((l: Index) => m2(k)(l) * m3(l)(j)), (k: Index) => m1(i)(k) * mult(m2, m3)(k)(j)); }
        Sum((k: Index) => m1(i)(k) * mult(m2, m3)(k)(j));
        ==
        mult(m1, mult(m2, m3))(i)(j);
    }
}

lemma mult_assoc(m1: Matrix, m2: Matrix, m3: Matrix)
    ensures mult(mult(m1, m2), m3) == mult(m1, mult(m2, m3))
{
    forall i, j 
        ensures mult(mult(m1, m2), m3)(i)(j) == mult(m1, mult(m2, m3))(i)(j)
        { mult_assoc_ij(m1, m2, m3, i, j); }
    Same(mult(mult(m1, m2), m3), mult(m1, mult(m2, m3)));
}
