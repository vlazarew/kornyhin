/***************************************
Этот модуль описывает типы данных для представления
ориентированных графов, их вершин и дуг.

Граф представлен в типе `Graph`.

Поле `vertices` описывает вершины графа. Это массив из `vsize` значений
типа `Vertex`. Тип `Vertex` описывает размещение некоторой вершины графа
в массиве `vertices`. Поле `existent` в элементе массива `vertices` с
некоторым индексом `i` равно истине (т.е. не равно 0) тогда, когда в этом
элементе размещена вершина графа. В противном случае элемент массива
`vertices` с индексом `i` считается свободным.

Поле `edges` описывает дуги графа. Это массив из `esize` значений типа `Edge`.
Тип `Edge` описывает размещение некоторой дуги графа в массиве `edges`.
Поле `existent` в элементе массива `edges` имеет тот же смысл, что и то же
поле в элементе массива `vertices`. Поля `from` и `to` должны быть индексами в
массиве `vertices` и означают вершины, из которой исходит дуга и в которую
входит дуга.

Поле `ecnt` означает то количество первых элементов массива `edges`,
после которого все остальные элементы будут свободными.

Ниже приведено определение описанных типов и предикат `valid`, формально
описывающий инвариант типа `Graph`.

В конце модуля размещена функция `add_edge`, которая добавляет дугу в граф.
Ее аргумент `g` означает граф, в который надо
добавить дугу, аргументы `f` и `t` означают индексы в массиве `g->vertices`,
означающие начало и конец добавляемой дуги. Функция применима только
к графам, в которых есть свободное место для добавления дуги.
Перед функцией размещена ее формальная спецификация на языке `ACSL`.
****************************************/


typedef struct {
    int payload;
    int existent;
} Vertex;

typedef struct {
	int from;
	int to;
	int existent;
} Edge;

typedef struct {
	Vertex *vertices;
	int vsize;
	Edge *edges;
	int ecnt;
	int esize;
} Graph;

/*@
    predicate is_vertex(Graph *g, integer v) =
        0 <= v < g->vsize;

    predicate edge_valid(Graph *g, integer k) =
        g->edges[k].existent == 1 ==>
        is_vertex(g, g->edges[k].from) &&
        is_vertex(g, g->edges[k].to) &&
        g->vertices[g->edges[k].from].existent == 1 &&
        g->vertices[g->edges[k].to].existent == 1;

    predicate edges_valid(Graph *g, integer n) =
        \forall integer k; 0 <= k < n ==> edge_valid(g, k);

    predicate graph_valid(Graph *g) =
        g->vsize > 0 &&
        g->esize > 0 &&
        g->esize >= g->ecnt >= 0 &&
        \valid(g->vertices + (0 .. g->vsize - 1)) &&
        \valid(g->edges + (0 .. g->esize - 1)) &&
        edges_valid(g, g->ecnt) &&
        (\forall integer k; g->ecnt <= k < g->esize ==> g->edges[k].existent == 0);


    predicate edge_saved{L1, L2}(Graph *g, integer k) = \at(g->edges[k], L1) == \at(g->edges[k], L2);
    predicate edges_saved{L1, L2}(Graph *g, integer m, integer n) = \forall integer k; m <= k < n ==> edge_saved{L1, L2}(g, k);


    predicate full(Graph *g) = range_existent(g, 0, g->esize);
    predicate range_existent(Graph *g, integer m, integer n) = \forall integer k; m <= k < n ==> g->edges[k].existent == 1;*/
// */
//     
/*@ 

axiomatic EdgesCount {
    logic integer count{L}(Graph *g, integer f, integer t, integer m, integer n);

    axiom count_zero: \forall Graph *g, integer f, t, m, n; m >= n ==>
        count(g, f, t, m, n) == 0;

	predicate count_one_p{L}(Graph *g, integer f, integer t, integer m) =
        count(g, f, t, m, m + 1) == (g->edges[m].existent == 1 && g->edges[m].from == f && g->edges[m].to == t ? 1 : 0);

    axiom count_one{L}: \forall Graph *g, integer f, t, m; count_one_p(g, f, t, m);

    predicate count_split_p{L}(Graph *g, integer f, integer t, integer m, integer n, integer k) =
        count(g, f, t, m, k) == count(g, f, t, m, n) + count(g, f, t, n, k);

    axiom count_split{L}: \forall Graph *g, integer f, t, m, n, k; m <= n <= k ==>
        count_split_p(g, f, t, m, n, k);

    // axiom count_one: \forall Graph *g, integer f, t, m;
    //     count(g, f, t, m, m + 1) == (g->edges[m].existent == 1 && g->edges[m].from == f && g->edges[m].to == t ? 1 : 0);

    // axiom count_split: \forall Graph *g, integer f, t, m, n, k; 
    //     m <= n <= k ==> count(g, f, t, m, k) == count(g, f, t, m, n) + count(g, f, t, n, k);

    predicate count_saved_p{L1, L2}(Graph *g, integer f, integer t, integer m, integer n) =
            count{L1}(g, f, t, m, n) == count{L2}(g, f, t, m, n);

    axiom count_saved{L1, L2}: \forall Graph *g, integer f, t, m, n;
            edges_saved{L1, L2}(g, m, n) ==> count_saved_p{L1, L2}(g, f, t, m, n);

    axiom count_existent: \forall Graph *g, integer f, t, m, n;
            (\forall integer k; m <= k < n ==> g->edges[k].existent == 0) ==> count(g, f, t, m, n) == 0;

    logic integer all_count(Graph *g, integer f, integer t) = count(g, f, t, 0, g->esize);
}*/
// */

/*@
    requires \valid(g) && graph_valid(g);
    requires is_vertex(g, f);
    requires is_vertex(g, t);
    requires g->vertices[f].existent == 1;
    requires g->vertices[t].existent == 1;
    ensures \result == all_count(g, f, t);*/
// */
int
count(Graph *g, int f, int t)
{
    int c = 0;
    /*@
        loop invariant 0 <= i <= g->ecnt;
        loop invariant 0 <= c <= i;
        loop invariant c == count(g, f, t, 0, i);
        loop variant g->ecnt - i;
    */
    for (int i = 0; i < g->ecnt; ++i) {
        if (g->edges[i].existent && g->edges[i].from == f && g->edges[i].to == t) {
            ++ c;
        }
        /*@ assert count(g, f, t, 0, i + 1) == count(g, f, t, 0, i) + count(g, f, t, i, i + 1);*/
        /*@ assert count(g, f, t, 0, g->esize) == count(g, f, t, 0, i + 1) + count(g, f, t, i + 1, g->esize);*/
    }
    return c;
}

/*@
  requires \valid(g) && graph_valid(g);
  requires is_vertex(g, f);
  requires is_vertex(g, t);
  requires g->vertices[f].existent == 1;
  requires g->vertices[t].existent == 1;
  requires !full(g);
  ensures graph_valid(g);
  ensures all_count(g, f, t) == all_count{Pre}(g, f, t) + 1;
  ensures \forall integer f2, t2; (f2 != f || t2 != t) ==> all_count(g, f2, t2) == all_count{Pre}(g, f2, t2);*/
// */
void
add_edge(Graph *g, int f, int t)
{
    if (g->ecnt < g->esize) {
        g->edges[g->ecnt].from = f;
        g->edges[g->ecnt].to = t;
        g->edges[g->ecnt].existent = 1;
        /*@ assert edges_saved{Pre, Here}(g, 0, g->ecnt) &&
            edges_saved{Pre, Here}(g, g->ecnt + 1, g->esize);
        */
        /*@ assert edge_valid(g, g->ecnt);*/
        /*@ assert count(g, f, t, g->ecnt, g->ecnt + 1) == 1;*/
        /*@ assert \forall integer f2, t2; count{Pre}(g, f2, t2, g->ecnt, g->ecnt + 1) == 0;*/
        /*@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count(g, f2, t2, g->ecnt, g->ecnt + 1) == 0;*/
        /*@ assert \forall integer f2, t2; 
            count_saved_p{Pre, Here}(g, f2, t2, 0, g->ecnt) &&
            count_saved_p{Pre, Here}(g, f2, t2, g->ecnt + 1, g->esize);
        */
        /*@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count_saved_p{Pre, Here}(g, f2, t2, g->ecnt, g->ecnt + 1);*/
        /*@ assert \forall integer f2, t2; all_count(g, f2, t2) == all_count{Pre}(g, f2, t2) + count(g, f2, t2, g->ecnt, g->ecnt + 1);*/
        /*@ assert all_count(g, f, t) == count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->ecnt + 1) + count(g, f, t, g->ecnt + 1, g->esize);*/
        /*@ assert all_count{Pre}(g, f, t) == count{Pre}(g, f, t, 0, g->ecnt) + count{Pre}(g, f, t, g->ecnt, g->ecnt + 1) + count{Pre}(g, f, t, g->ecnt + 1, g->esize);*/
        ++ g->ecnt;
        return;
    }

    /*@ assert g->esize == g->ecnt;*/
    /*@
        loop invariant 0 <= i <= g->ecnt;
        loop invariant edges_saved{Pre, Here}(g, 0, g->ecnt);
        loop invariant \forall integer f2, t2; all_count{Pre}(g, f2, t2) == all_count{Here}(g, f2, t2);
        loop invariant range_existent(g, 0, i);
        loop variant g->ecnt - i;
    */
    for (int i = 0; i < g->ecnt; ++i) {
        /*@ ghost L:;*/
        if (!g->edges[i].existent) {
            g->edges[i].from = f;
            g->edges[i].to = t;
            g->edges[i].existent = 1;
            /*@ assert edges_saved{Pre, Here}(g, 0, i) &&
                edges_saved{Pre, Here}(g, i + 1, g->esize);
            */
            /*@ assert edge_valid(g, i);*/
            /*@ assert count(g, f, t, i, i + 1) == 1;*/
            /*@ assert \forall integer f2, t2; count{Pre}(g, f2, t2, i, i + 1) == 0;*/
            /*@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count(g, f2, t2, i, i + 1) == 0;*/
            /*@ assert \forall integer f2, t2; 
                count_saved_p{Pre, Here}(g, f2, t2, 0, i) &&
                count_saved_p{Pre, Here}(g, f2, t2, i + 1, g->esize);
            */
            /*@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count_saved_p{Pre, Here}(g, f2, t2, i, i + 1);*/
            /*@ assert \forall integer f2, t2; all_count(g, f2, t2) == count(g, f2, t2, 0, i) + count(g, f2, t2, i, i + 1) + count(g, f2, t2, i + 1, g->esize);*/
            /*@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> all_count(g, f2, t2) == all_count{Pre}(g, f2, t2);*/
            /*@ assert all_count{Pre}(g, f, t) == count{Pre}(g, f, t, 0, i) + count{Pre}(g, f, t, i, i + 1) + count{Pre}(g, f, t, i + 1, g->esize);*/
            return;
        }
        /*@ assert edges_saved{L, Here}(g, 0, g->ecnt);*/
        /*@ assert \forall integer f2, t2; all_count{L}(g, f2, t2) == all_count{Here}(g, f2, t2);*/
    }
    /*@ assert full(g);*/
}
// 
