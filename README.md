# NextPermutationOnSubsegment
Реализована структура данных, позволяющая:
1) находить сумму на подотрезке [l,r]
2) вставить элемент x в позицию pos
3) удалить элемент x, находящийся на позиции i
4) присвоить элемент x на подотрезке [l, r]
5) прибавить число x на подотрезке [l, r]
6) next_permutation на подотрезке [l, r]
7) prev_permutation на подотрезке [l, r]

Все операции работают за O(logn) 
Эта структура работает на **Splay-tree** с технологией отложенных операций.
