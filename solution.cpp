#include <bits/stdc++.h>
using namespace std;

using ll = long long;

static const double DEFAULT_TIME_LIMIT_SEC = 290.0;

struct FastTimer {
    chrono::steady_clock::time_point start;
    double limitSec;

    FastTimer() {
        start = chrono::steady_clock::now();
        const char* env = std::getenv("MWIS_TIME_LIMIT_SEC");
        if (env) {
            limitSec = max(0.1, atof(env));
        } else {
            limitSec = DEFAULT_TIME_LIMIT_SEC;
        }
    }

    inline double elapsed() const {
        return chrono::duration<double>(chrono::steady_clock::now() - start).count();
    }

    inline bool timeUp() const {
        return elapsed() >= limitSec;
    }
};

struct RNG {
    mt19937_64 eng;
    RNG() : eng((uint64_t)chrono::steady_clock::now().time_since_epoch().count()) {}
    inline int nextInt(int l, int r) {
        return uniform_int_distribution<int>(l, r)(eng);
    }
    inline double nextDoubleSigned() {
        return uniform_real_distribution<double>(-1.0, 1.0)(eng);
    }
};

int N, M;
vector<ll> W;
vector<int> head, to, nxt, deg;
vector<ll> sumNbrW;
int edgePtr = 0;

inline void addEdge(int u, int v) {
    to[edgePtr] = v;
    nxt[edgePtr] = head[u];
    head[u] = edgePtr++;
}

vector<char> fixedSel;
ll fixedScore = 0;

vector<int> parentTmp;
vector<int> curDeg;
vector<char> inCycle;
vector<ll> dp0, dp1;

void solveTreeComponent(const vector<int>& comp) {
    if (comp.empty()) return;
    int root = comp[0];
    for (int v : comp) parentTmp[v] = -2;

    vector<int> order;
    order.reserve(comp.size());
    vector<int> st;
    st.push_back(root);
    parentTmp[root] = -1;

    while (!st.empty()) {
        int v = st.back();
        st.pop_back();
        order.push_back(v);
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (parentTmp[u] == -2) {
                parentTmp[u] = v;
                st.push_back(u);
            }
        }
    }

    for (int i = (int)order.size() - 1; i >= 0; --i) {
        int v = order[i];
        ll take = W[v];
        ll skip = 0;
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (parentTmp[u] == v) {
                take += dp0[u];
                skip += max(dp0[u], dp1[u]);
            }
        }
        dp0[v] = skip;
        dp1[v] = take;
    }

    fixedScore += max(dp0[root], dp1[root]);
    vector<pair<int, bool>> st2;
    st2.push_back({root, dp1[root] > dp0[root]});
    while (!st2.empty()) {
        auto [v, takeV] = st2.back();
        st2.pop_back();
        if (takeV) fixedSel[v] = 1;
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (parentTmp[u] == v) {
                bool takeU = (!takeV) && (dp1[u] > dp0[u]);
                st2.push_back({u, takeU});
            }
        }
    }
}

ll solvePathOnGain(const vector<ll>& gain, int l, int r, vector<char>& pick) {
    if (l > r) return 0;
    int len = r - l + 1;
    vector<ll> take(len), skip(len);
    take[0] = gain[l];
    skip[0] = 0;
    for (int i = 1; i < len; ++i) {
        skip[i] = max(skip[i - 1], take[i - 1]);
        take[i] = skip[i - 1] + gain[l + i];
    }
    ll best = max(skip[len - 1], take[len - 1]);
    int i = len - 1;
    while (i >= 0) {
        if (take[i] > skip[i]) {
            pick[l + i] = 1;
            i -= 2;
        } else {
            pick[l + i] = 0;
            --i;
        }
    }
    return best;
}

void solveUnicyclicComponent(const vector<int>& comp) {
    if (comp.empty()) return;
    for (int v : comp) {
        curDeg[v] = deg[v];
        parentTmp[v] = -2;
        inCycle[v] = 1;
        dp0[v] = dp1[v] = 0;
    }

    vector<int> q;
    q.reserve(comp.size());
    for (int v : comp) {
        if (curDeg[v] == 1) q.push_back(v);
    }

    for (size_t qi = 0; qi < q.size(); ++qi) {
        int v = q[qi];
        if (curDeg[v] == 0) continue;
        curDeg[v] = 0;
        inCycle[v] = 0;
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (curDeg[u] > 0) {
                --curDeg[u];
                if (curDeg[u] == 1) q.push_back(u);
            }
        }
    }

    int start = -1;
    for (int v : comp) {
        if (inCycle[v]) {
            start = v;
            break;
        }
    }
    if (start == -1) {
        solveTreeComponent(comp);
        return;
    }

    vector<int> cycle;
    cycle.reserve(comp.size());
    int prev = -1, cur = start;
    do {
        cycle.push_back(cur);
        int nxtCycle = -1;
        for (int e = head[cur]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (inCycle[u] && u != prev) {
                nxtCycle = u;
                break;
            }
        }
        prev = cur;
        cur = nxtCycle;
    } while (cur != start && cur != -1);

    int L = (int)cycle.size();
    vector<int> order;
    order.reserve(max(0, (int)comp.size() - L));
    vector<int> st;
    st.reserve(comp.size());

    for (int c : cycle) {
        for (int e = head[c]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (!inCycle[u] && parentTmp[u] == -2) {
                parentTmp[u] = c;
                st.push_back(u);
                while (!st.empty()) {
                    int v = st.back();
                    st.pop_back();
                    order.push_back(v);
                    for (int ee = head[v]; ee != -1; ee = nxt[ee]) {
                        int wv = to[ee];
                        if (!inCycle[wv] && parentTmp[wv] == -2) {
                            parentTmp[wv] = v;
                            st.push_back(wv);
                        }
                    }
                }
            }
        }
    }

    for (int i = (int)order.size() - 1; i >= 0; --i) {
        int v = order[i];
        ll take = W[v], skip = 0;
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (!inCycle[u] && parentTmp[u] == v) {
                take += dp0[u];
                skip += max(dp0[u], dp1[u]);
            }
        }
        dp0[v] = skip;
        dp1[v] = take;
    }

    vector<ll> base0(L), gain(L);
    ll baseSum = 0;
    for (int i = 0; i < L; ++i) {
        int c = cycle[i];
        ll s0 = 0, s1 = W[c];
        for (int e = head[c]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (!inCycle[u]) {
                s1 += dp0[u];
                s0 += max(dp0[u], dp1[u]);
            }
        }
        base0[i] = s0;
        gain[i] = s1 - s0;
        baseSum += s0;
    }

    vector<char> pick0(L, 0), pick1(L, 0);
    ll extra0 = 0, extra1 = 0;
    if (L == 1) {
        extra1 = gain[0];
        pick1[0] = 1;
    } else {
        extra0 = solvePathOnGain(gain, 1, L - 1, pick0);
        pick1[0] = 1;
        if (L > 2) extra1 = gain[0] + solvePathOnGain(gain, 1, L - 2, pick1);
        else extra1 = gain[0];
    }

    const vector<char>& cycPick = (extra1 > extra0 ? pick1 : pick0);
    fixedScore += baseSum + max(extra0, extra1);

    vector<pair<int, bool>> st2;
    st2.reserve(comp.size());
    for (int i = 0; i < L; ++i) {
        int c = cycle[i];
        if (cycPick[i]) fixedSel[c] = 1;
        bool parentSelected = cycPick[i];
        for (int e = head[c]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (!inCycle[u] && parentTmp[u] == c) {
                st2.push_back({u, parentSelected});
            }
        }
    }
    while (!st2.empty()) {
        auto [v, parentSelected] = st2.back();
        st2.pop_back();
        bool takeV = (!parentSelected) && (dp1[v] > dp0[v]);
        if (takeV) fixedSel[v] = 1;
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (!inCycle[u] && parentTmp[u] == v) {
                st2.push_back({u, takeV});
            }
        }
    }
}

struct State {
    vector<char> sel;
    vector<char> inHeap;
    vector<int> pos;
    vector<int> selList;
    vector<ll> block;
    ll score = 0;

    State() {}
    explicit State(int n) { init(n); }

    void init(int n) {
        sel.assign(n + 1, 0);
        inHeap.assign(n + 1, 0);
        pos.assign(n + 1, -1);
        block.assign(n + 1, 0);
        selList.clear();
        score = 0;
    }

    void clearAll() {
        fill(sel.begin(), sel.end(), 0);
        fill(inHeap.begin(), inHeap.end(), 0);
        fill(pos.begin(), pos.end(), -1);
        fill(block.begin(), block.end(), 0);
        selList.clear();
        score = 0;
    }
};

inline void eraseSelected(State& st, int v) {
    int idx = st.pos[v];
    int last = st.selList.back();
    st.selList[idx] = last;
    st.pos[last] = idx;
    st.selList.pop_back();
    st.pos[v] = -1;
    st.sel[v] = 0;
    st.score -= W[v];
    st.block[v] = 0;
    for (int e = head[v]; e != -1; e = nxt[e]) {
        int u = to[e];
        st.block[u] -= W[v];
    }
}

inline void addSelected(State& st, int v) {
    st.sel[v] = 1;
    st.pos[v] = (int)st.selList.size();
    st.selList.push_back(v);
    st.score += W[v];
    st.block[v] = 0;
    for (int e = head[v]; e != -1; e = nxt[e]) {
        int u = to[e];
        st.block[u] += W[v];
    }
}

inline void tryPushVertex(int v, State& st, priority_queue<pair<ll,int>>& pq) {
    if (st.sel[v]) return;
    ll gain = W[v] - st.block[v];
    if (gain > 0 && !st.inHeap[v]) {
        st.inHeap[v] = 1;
        pq.push({gain, v});
    }
}

void greedyBuild(State& st, const vector<int>& order) {
    st.clearAll();
    for (int v : order) {
        if (!st.sel[v] && st.block[v] == 0) {
            addSelected(st, v);
        }
    }
}

void initHeapFromState(State& st, const vector<int>& active, priority_queue<pair<ll,int>>& pq) {
    while (!pq.empty()) pq.pop();
    fill(st.inHeap.begin(), st.inHeap.end(), 0);
    for (int v : active) {
        if (!st.sel[v]) {
            ll gain = W[v] - st.block[v];
            if (gain > 0) {
                st.inHeap[v] = 1;
                pq.push({gain, v});
            }
        }
    }
}

void localImprove(State& st, const vector<int>& active, const FastTimer& timer) {
    priority_queue<pair<ll,int>> pq;
    initHeapFromState(st, active, pq);
    vector<int> removed;
    removed.reserve(64);

    int checkCounter = 0;
    while (!pq.empty()) {
        if ((++checkCounter & 1023) == 0 && timer.timeUp()) break;
        auto [g, v] = pq.top();
        pq.pop();
        st.inHeap[v] = 0;
        if (st.sel[v]) continue;
        ll curGain = W[v] - st.block[v];
        if (curGain <= 0) continue;

        removed.clear();
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (st.sel[u]) removed.push_back(u);
        }

        for (int u : removed) {
            eraseSelected(st, u);
            for (int e = head[u]; e != -1; e = nxt[e]) {
                int x = to[e];
                tryPushVertex(x, st, pq);
            }
        }
        addSelected(st, v);
    }
}

void perturbState(State& st, RNG& rng) {
    if (st.selList.empty()) return;
    int s = (int)st.selList.size();
    int k = max(5, min(400, s / 40 + 1));
    vector<int> removed;
    removed.reserve(k);
    for (int i = 0; i < k && !st.selList.empty(); ++i) {
        int idx = rng.nextInt(0, (int)st.selList.size() - 1);
        int v = st.selList[idx];
        removed.push_back(v);
        eraseSelected(st, v);
    }
    fill(st.inHeap.begin(), st.inHeap.end(), 0);
    priority_queue<pair<ll,int>> pq;
    for (int u : removed) {
        for (int e = head[u]; e != -1; e = nxt[e]) {
            int x = to[e];
            tryPushVertex(x, st, pq);
        }
    }
    vector<int> removedLocal;
    removedLocal.reserve(64);
    int checkCounter = 0;
    while (!pq.empty()) {
        if ((++checkCounter & 1023) == 0 && false) break;
        auto [g, v] = pq.top();
        pq.pop();
        st.inHeap[v] = 0;
        if (st.sel[v]) continue;
        ll curGain = W[v] - st.block[v];
        if (curGain <= 0) continue;
        removedLocal.clear();
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (st.sel[u]) removedLocal.push_back(u);
        }
        for (int u : removedLocal) {
            eraseSelected(st, u);
            for (int e = head[u]; e != -1; e = nxt[e]) {
                int x = to[e];
                tryPushVertex(x, st, pq);
            }
        }
        addSelected(st, v);
    }
}

vector<int> buildDegeneracyOrder(const vector<int>& active) {
    vector<int> cur(N + 1, 0);
    vector<char> removed(N + 1, 0);
    priority_queue<pair<int,int>, vector<pair<int,int>>, greater<pair<int,int>>> pq;
    for (int v : active) {
        cur[v] = deg[v];
        pq.push({cur[v], v});
    }
    vector<int> peel;
    peel.reserve(active.size());
    while (!pq.empty()) {
        auto [d, v] = pq.top();
        pq.pop();
        if (removed[v] || d != cur[v]) continue;
        removed[v] = 1;
        peel.push_back(v);
        for (int e = head[v]; e != -1; e = nxt[e]) {
            int u = to[e];
            if (!removed[u]) {
                --cur[u];
                pq.push({cur[u], u});
            }
        }
    }
    reverse(peel.begin(), peel.end());
    return peel;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    cin >> N >> M;
    W.assign(N + 1, 0);
    for (int i = 1; i <= N; ++i) cin >> W[i];

    head.assign(N + 1, -1);
    to.assign(2 * M + 5, 0);
    nxt.assign(2 * M + 5, 0);
    deg.assign(N + 1, 0);
    sumNbrW.assign(N + 1, 0);
    edgePtr = 0;

    for (int i = 0; i < M; ++i) {
        int u, v;
        cin >> u >> v;
        addEdge(u, v);
        addEdge(v, u);
        ++deg[u];
        ++deg[v];
    }

    for (int v = 1; v <= N; ++v) {
        ll s = 0;
        for (int e = head[v]; e != -1; e = nxt[e]) s += W[to[e]];
        sumNbrW[v] = s;
    }

    fixedSel.assign(N + 1, 0);
    parentTmp.assign(N + 1, -2);
    curDeg.assign(N + 1, 0);
    inCycle.assign(N + 1, 0);
    dp0.assign(N + 1, 0);
    dp1.assign(N + 1, 0);

    vector<char> vis(N + 1, 0);
    vector<int> comp;
    comp.reserve(1024);
    vector<int> stackNodes;
    stackNodes.reserve(1024);
    vector<int> active;
    active.reserve(N);

    for (int s = 1; s <= N; ++s) {
        if (vis[s]) continue;
        comp.clear();
        long long degSum = 0;
        stackNodes.clear();
        stackNodes.push_back(s);
        vis[s] = 1;
        while (!stackNodes.empty()) {
            int v = stackNodes.back();
            stackNodes.pop_back();
            comp.push_back(v);
            degSum += deg[v];
            for (int e = head[v]; e != -1; e = nxt[e]) {
                int u = to[e];
                if (!vis[u]) {
                    vis[u] = 1;
                    stackNodes.push_back(u);
                }
            }
        }
        long long edgesInComp = degSum / 2;
        if (edgesInComp == (long long)comp.size() - 1) {
            solveTreeComponent(comp);
        } else if (edgesInComp == (long long)comp.size()) {
            solveUnicyclicComponent(comp);
        } else {
            for (int v : comp) active.push_back(v);
        }
    }

    FastTimer timer;
    RNG rng;
    double deadline = timer.limitSec;
    auto timeCheck = [&]() -> bool { return timer.elapsed() >= deadline; };

    State best(N), cur(N);
    best.clearAll();
    cur.clearAll();

    if (!active.empty()) {
        vector<int> orderWeight = active;
        vector<int> orderRatio1 = active;
        vector<int> orderRatio2 = active;
        vector<int> orderPenalty = active;
        vector<int> orderDeg = active;
        vector<int> orderRand1 = active;
        vector<int> orderRand2 = active;
        vector<int> orderDegeneracy = buildDegeneracyOrder(active);

        vector<double> keyWeight(N + 1), keyRatio1(N + 1), keyRatio2(N + 1), keyPenalty(N + 1), keyRand1(N + 1), keyRand2(N + 1);
        for (int v : active) {
            keyWeight[v] = (double)W[v];
            keyRatio1[v] = (double)W[v] / (double)(deg[v] + 1);
            keyRatio2[v] = (double)W[v] / sqrt((double)deg[v] + 1.0);
            keyPenalty[v] = (double)W[v] - 0.35 * (double)sumNbrW[v] / (double)(deg[v] + 1);
            keyRand1[v] = keyRatio1[v] * (1.0 + 0.03 * rng.nextDoubleSigned());
            keyRand2[v] = keyWeight[v] * (1.0 + 0.02 * rng.nextDoubleSigned());
        }

        auto sortByKey = [&](vector<int>& ord, const vector<double>& key) {
            sort(ord.begin(), ord.end(), [&](int a, int b) {
                if (key[a] != key[b]) return key[a] > key[b];
                return a < b;
            });
        };

        sortByKey(orderWeight, keyWeight);
        sortByKey(orderRatio1, keyRatio1);
        sortByKey(orderRatio2, keyRatio2);
        sortByKey(orderPenalty, keyPenalty);
        sort(orderDeg.begin(), orderDeg.end(), [&](int a, int b) {
            if (deg[a] != deg[b]) return deg[a] < deg[b];
            if (W[a] != W[b]) return W[a] > W[b];
            return a < b;
        });
        sortByKey(orderRand1, keyRand1);
        sortByKey(orderRand2, keyRand2);

        vector<vector<int>> orders;
        orders.push_back(orderWeight);
        orders.push_back(orderRatio1);
        orders.push_back(orderRatio2);
        orders.push_back(orderPenalty);
        orders.push_back(orderDeg);
        orders.push_back(orderDegeneracy);
        orders.push_back(orderRand1);
        orders.push_back(orderRand2);

        int initialRounds = min<int>((int)orders.size(), 8);
        for (int i = 0; i < initialRounds && !timeCheck(); ++i) {
            greedyBuild(cur, orders[i]);
            localImprove(cur, active, timer);
            if (cur.score > best.score) best = cur;
        }

        if (best.selList.empty()) {
            greedyBuild(best, orderWeight);
            localImprove(best, active, timer);
        }

        cur = best;

        int round = 0;
        while (!timeCheck()) {
            ++round;
            if ((round & 1) == 0) {
                cur = best;
                perturbState(cur, rng);
            } else {
                const vector<int>& ord = orders[rng.nextInt(0, (int)orders.size() - 1)];
                greedyBuild(cur, ord);
            }
            localImprove(cur, active, timer);
            if (cur.score > best.score) {
                best = cur;
            }
            if ((round & 7) == 0 && timeCheck()) break;
        }
    }

    ll totalScore = fixedScore + best.score;
    vector<int> answer;
    answer.reserve(N);
    for (int v = 1; v <= N; ++v) {
        if (fixedSel[v] || best.sel[v]) answer.push_back(v);
    }
    sort(answer.begin(), answer.end());
    answer.erase(unique(answer.begin(), answer.end()), answer.end());

    cout << totalScore << '\n';
    for (size_t i = 0; i < answer.size(); ++i) {
        if (i) cout << ' ';
        cout << answer[i];
    }
    cout << '\n';
    return 0;
}