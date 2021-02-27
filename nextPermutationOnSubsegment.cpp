#include <iostream>
#include <cassert>

using namespace std;

using ll = long long;

const ll EMP = 224224224;
const ll inf = 1e14;

struct node {
    node* l = nullptr;
    node* r = nullptr;
    ll sz = 1;
    ll prior;
    int rev = 0;
    ll val;
    ll equ = EMP;
    ll add = 0;
    ll sum;
    ll minn;
    ll maxx;
    int dec_syf = 1;
    int inc_syf = 1;
    int dec_pref = 1;
    int inc_pref = 1;
    ll leftest;
    ll rightest;
    node* par = nullptr;
    node(ll val): prior(rand()), val(val), sum(val), minn(val), maxx(val), leftest(val), rightest(val) {}
};

ll gsz(node* v) {
    if (!v)
        return 0;
    return v->sz;
}

ll gsum(node* v) {
    if (!v)
        return 0;
    if (v->equ == EMP)
        return v->sum + gsz(v) * v->add;
    return (v->equ + v->add) * gsz(v);
}

ll gmin(node* v) {
    if (!v)
        return inf;
    if (v->equ == EMP)
        return v->add + v->minn;
    return v->add + v->equ;
}

ll gmax(node* v) {
    if (!v)
        return -inf;
    if (v->equ == EMP)
        return v->add + v->maxx;
    return v->add + v->equ;
}

node* get_p(node* v) {
    if (!v)
        return nullptr;
    return v->par;
}

node* get_g(node* v) {
    return get_p(get_p(v));
}

void push(node* v) {
    if (!v)
        return;
    v->sum = gsum(v);
    v->minn = gmin(v);
    v->maxx = gmax(v);
    v->val += v->add;
    v->leftest += v->add;
    v->rightest += v->add;

    if (v->l) {
        v->l->add += v->add;
        v->l->par = v;
        v->l->rev ^= v->rev;
    }
    if (v->r) {
        v->r->add += v->add;
        v->r->rev ^= v->rev;
        v->r->par = v;
    }

    if (v->equ != EMP)
        v->equ += v->add;

    v->add = 0;

    if (v->rev) {
        swap(v->l, v->r);
        swap(v->leftest, v->rightest);
        swap(v->dec_syf, v->inc_pref);
        swap(v->inc_syf, v->dec_pref);
        v->rev = 0;
    }

    if (v->equ != EMP) {
        v->val = v->equ;
        v->leftest = v->rightest = v->equ;
        int sz = gsz(v);
        v->dec_pref = v->dec_syf = sz;
        v->inc_pref = v->inc_syf = sz;
        if (v->l) {
            v->l->add = 0;
            v->l->equ = v->equ;
        }
        if (v->r) {
            v->r->add = 0;
            v->r->equ = v->equ;
        }
        v->equ = EMP;
    }
}

void up(node* v) {
    if (!v)
        return;
    push(v->l);
    push(v->r);

    v->sz = gsz(v->l) + gsz(v->r) + 1;
    v->sum = gsum(v->l) + gsum(v->r) + v->val;
    v->minn = min(gmin(v->l), min(v->val, gmin(v->r)));
    v->maxx = max(gmax(v->l), max(v->val, gmax(v->r)));
    v->leftest = v->val;
    v->rightest = v->val;

    v->dec_pref = 1;
    v->dec_syf = 1;
    v->inc_pref = 1;
    v->inc_syf = 1;

    if (v->l) {
        v->leftest = v->l->leftest;
        v->l->par = v;
    }
    if (v->r) {
        v->rightest = v->r->rightest;
        v->r->par = v;
    }

    if (!v->l && !v->r)
        return;

    if (v->r) {
        if (v->val <= v->r->leftest)
            v->inc_pref += v->r->inc_pref;

        if (v->val >= v->r->leftest)
            v->dec_pref += v->r->dec_pref;
    }

    if (v->l) {
        if (v->l->rightest <= v->val)
            v->inc_syf += v->l->inc_syf;

        if (v->l->rightest >= v->val)
            v->dec_syf += v->l->dec_syf;
    }

    if (v->r) {
        v->dec_syf = v->r->dec_syf;
        if (v->r->dec_syf == gsz(v->r) && v->val >= v->r->leftest) {
            ++v->dec_syf;
            if (v->l && v->val <= v->l->rightest)
                v->dec_syf += v->l->dec_syf;
        }

        v->inc_syf = v->r->inc_syf;
        if (v->r->inc_syf == gsz(v->r) && v->val <= v->r->leftest) {
            ++v->inc_syf;
            if (v->l && v->l->rightest <= v->val)
                v->inc_syf += v->l->inc_syf;
        }
    }

    if (v->l) {
        v->inc_pref = v->l->inc_pref;
        if (v->l->inc_pref == gsz(v->l) && v->l->rightest <= v->val) {
            ++v->inc_pref;
            if (v->r && v->val <= v->r->leftest)
                v->inc_pref += v->r->inc_pref;
        }

        v->dec_pref = v->l->dec_pref;
        if (v->l->dec_pref == gsz(v->l) && v->l->rightest >= v->val) {
            ++v->dec_pref;
            if (v->r && v->val >= v->r->leftest)
                v->dec_pref += v->r->dec_pref;
        }
    }
}

node* rotate(node* x) {
    push(x);
    bool lef = false;
    node* p = get_p(x);
    node* h = get_p(p);
    node* b;
    push(p);
    push(x);
    if (h && h->l == p)
        lef = true;
    x->par = nullptr;
    if (p->l == x) {
        b = x->r;
        p->l = nullptr;
        p->l = b;
        x->r = p;
    } else {
        b = x->l;
        p->r = nullptr;
        p->r = b;
        x->l = p;
    }
    up(p);
    up(x);
    if (x)
        x->par = h;
    if (h) {
        if (lef)
            h->l = x;
        else
            h->r = x;
        up(h);
    }
    return x;
}

bool is_zig(node* x) {
    return x && get_p(x) && !get_g(x);
}

node* zig(node* x) {
    x = rotate(x);
    x->par = nullptr;
    return x;
}

bool is_zig_zig(node* x) {
    node* p = get_p(x);
    node* g = get_g(x);
    if (!x || !p || !g)
        return false;
    if ((g->l == p && p->l == x) || (g->r == p && p->r == x))
        return true;
    return false;
}

node* zig_zig(node* x) {
    node* p = get_p(x);
    node* g = get_g(x);
    p = rotate(p);
    x = rotate(x);
    return x;
}

bool is_zig_zag(node* x) {
    node* p = get_p(x);
    node* g = get_g(x);
    if (!x || !p || !g)
        return false;
    if ((g->l == p && p->r == x) || (g->r == p && p->l == x))
        return true;
    return false;
}
node* zig_zag(node* x) {
    node* p = get_p(x);
    node* g = get_g(x);
    x = rotate(x);
    x = rotate(x);
    return x;
}

node* splay(node* v) {
    while (v) {
        if (!get_p(v))
            return v;
        if (is_zig(v)) {
            v = zig(v);
            return v;
        }
        if (is_zig_zig(v)) {
            v = zig_zig(v);
            continue;
        }
        if (is_zig_zag(v)) {
            v = zig_zag(v);
            continue;
        }
    }
}

node* search(node* x, int cnt) {
    push(x);
    int sz = gsz(x->l);
    if (sz == cnt)
        return x;
    if (sz < cnt)
        return search(x->r, cnt - sz - 1);
    return search(x->l, cnt);
}

pair<node*, node*> split(node* v, int cnt) {
    if (!v)
        return {nullptr, nullptr};
    push(v);
    if (gsz(v) == cnt) {
        return {v, nullptr};
    }
    v = search(v, cnt);
    v = splay(v);
    node* left = v->l;
    v->l = nullptr;
    up(v);
    if (left)
        left->par = nullptr;
    return {left, v};
}

node* merge(node* l, node* r) {
    push(l);
    push(r);
    if (!l)
        return r;
    if (!r)
        return l;
    while (l->r) {
        l = l->r;
        push(l);
    }
    l = splay(l);
    l->r = r;
    up(l);
    l->par = nullptr;
    return l;
}

ll sum(node*& v, int l, int r) {
    pair<node*, node*> s1 = split(v, l);
    pair<node*, node*> s2 = split(s1.second, r - l + 1);
    ll ans = gsum(s2.first);
    v = merge(s1.first, merge(s2.first, s2.second));
    return ans;
}

node* insert(node* v, node* ne, int pos) {
    pair<node*, node*> s1 = split(v, pos);
    v = merge(s1.first, merge(ne, s1.second));
    return v;
}

pair<node*, ll> delet(node* v, int pos) {
    pair<node*, node*> s1 = split(v, pos);
    pair<node*, node*> s2 = split(s1.second, 1);
    ll val = s2.first->val;
    delete s2.first;
    v = merge(s1.first, s2.second);
    return {v, val};
}

node* equ_segm(node* v, int l, int r, ll x) {
    pair<node*, node*> sp = split(v, l);
    pair<node*, node*> sp1 = split(sp.second, r - l + 1);
    sp1.first->equ = x;
    sp1.first->add = 0;
    v = merge(sp.first, merge(sp1.first, sp1.second));
    return v;
}

node* add_segm(node* v, int l, int r, ll x) {
    pair<node*, node*> sp = split(v, l);
    pair<node*, node*> sp1 = split(sp.second, r - l + 1);
    sp1.first->add += x;
    v = merge(sp.first, merge(sp1.first, sp1.second));
    return v;
}

ll get_decrease(node* v, ll x) {
    if (!v)
        return 0;
    push(v);
    int sz = gsz(v->l);
    if (gmax(v->r) > x) {
        return get_decrease(v->r, x) + sz + 1;
    }
    if (v->val > x)
        return sz;
    return get_decrease(v->l, x);
}

ll get_increase(node* v, ll x) {
    if (!v)
        return 0;
    push(v);
    ll sz = gsz(v->l);
    if (gmin(v->r) < x)
        return get_increase(v->r, x) + sz + 1;
    if (v->val < x)
        return sz;
    return get_increase(v->l, x);
}

node* do_perm(node* v, int l0, int r0, int (node::*syf_ptr), ll (*get_id) (node*, ll)) {
    pair<node*, node*> sp = split(v, l0);
    pair<node*, node*> sp1 = split(sp.second, r0 - l0 + 1);
    node* r = sp1.first;
    int syff = r->*syf_ptr;
    if (syff == gsz(r)) {
        r->rev ^= 1;
        v = merge(sp.first, merge(sp1.first, sp1.second));
        return v;
    }
    pair<node*, node*> sp2 = split(r, gsz(r) - syff - 1);
    node* segm = sp2.second;
    ll val = segm->leftest;
    segm = delet(segm, 0).first;

    int Ll = (*get_id)(segm, val);

    pair<node*, ll> x = delet(segm, Ll);
    segm = x.first;
    ll val1 = x.second;
    node* young = new node(val);
    segm = insert(segm, young, Ll);
    segm->rev ^= 1;
    node* y1 = new node(val1);
    segm = merge(y1, segm);
    v = merge(sp.first, merge(merge(sp2.first, segm), sp1.second));
    return v;
}

node* next_perm(node* v, int l0, int r0) {
    return do_perm(v, l0, r0, &node::dec_syf, get_decrease);
}

node* prev_perm(node* v, int l0, int r0) {
    return do_perm(v, l0, r0, &node::inc_syf, get_increase);
}

void print(node* v) {
    if (!v)
        return;
	push(v);
    print(v->l);
    cout << v->val << " ";
    print(v->r);
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(0);
    cout.tie(0);
    node* root = nullptr;
    int n;
    cin >> n;
    for (int i = 0; i < n; ++i) {
        ll x;
        cin >> x;
        root = insert(root, new node(x), i);
    }
    int q;
    cin >> q;
    while (q--) {
        int t;
        cin >> t;
        if (t == 1) {
            int l, r;
            cin >> l >> r;
            cout << sum(root, l, r) << "\n";
        }
        if (t == 2) {
            int x, pos;
            cin >> x >> pos;
            root = insert(root, new node(x), pos);
        }
        if (t == 3) {
            int pos;
            cin >> pos;
            root = delet(root, pos).first;
        }
        if (t == 4) {
            int x, l, r;
            cin >> x >> l >> r;
            root = equ_segm(root, l, r, x);
        }
        if (t == 5) {
            int x, l, r;
            cin >> x >> l >> r;
            root = add_segm(root, l, r, x);
        }
        if (t == 6) {
            int l, r;
            cin >> l >> r;
            root = next_perm(root, l, r);
        }
        if (t == 7) {
            int l, r;
            cin >> l >> r;
            root = prev_perm(root, l, r);
        }
    }
    print(root);
}
