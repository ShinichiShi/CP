/*
    “I'll take a potato chip...and eat it!”
*/
#include <bits/stdc++.h>
using namespace std;
#define int long long
#define ll long long
#define ios                           \
    ios_base::sync_with_stdio(false); \
    cin.tie(NULL);
#define f(i, t, n) for (int i = t; i <= n; i++)
#define fr(n) for (int i = 0; i < n; i++)
#define all(x) x.begin(), x.end()
#define rall(x) x.begin(), x.end(), greater<int>()
#define vvi vector<vector<int>>
#define vi vector<int>
#define vs vector<string>
#define vc vector<char>
#define pii pair<int, int>
#define pb push_back
#define acc(x) accumulate(x.begin(), x.end(), 0)
#define inp(v)        \
    for (auto &i : v) \
    {                 \
        cin >> i;     \
    }
#define out(x)            \
    for (auto i : x)      \
    {                     \
        cout << i << " "; \
    }
#define maxim(x) *max_element(x.begin(), x.end())
#define minim(x) *min_element(x.begin(), x.end())
#define cnt(x, n) count(x.begin(), x.end(), n)
#define fin(x, n) find(x.begin(), x.end(), n)
#define lower(v, x) lower_bound(v.begin(), v.end(), x) - v.begin()
#define ff first
#define ss second
#define mii map<int, int>
#define si set<int>
#define endl '\n'
#define nl cout << '\n';
#pragma GCC optimize "O3,omit-frame-pointer,inline"
#pragma GCC optimize("Ofast")
// #pragma GCC target ("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx")
#pragma GCC target("sse,sse2,mmx")
// __________________________GLOBAL VARS_______________________________________________
const int N = 1e6 + 5;
const int mx = 100'007;
const int mod = 100'000'007;
const int INF = 1e18;
int chk_prime[N];
vector<char> check_Prime;
vector<int> Prime, OneFac;
// vvi v(n, vector<int>(m, 0));
// __________________________FUNCTIONS_______________________________________________
void yes() { cout << "YES" << endl; }
void no() { cout << "NO" << endl; }
void minus() { cout << "-1" << endl; }
// Function to generate primes using linear sieve algorithm
void GetPrime(int n)
{
    check_Prime.resize(n + 1, 1);
    check_Prime[1] = 1;

    for (int i = 2; i <= n; i++)
    {
        if (check_Prime[i])
            Prime.push_back(i);

        for (int j = 0; j < Prime.size() && i * Prime[j] <= n; j++)
        {
            check_Prime[i * Prime[j]] = 0;
            OneFac[i * Prime[j]] = Prime[j];

            if (i % Prime[j] == 0)
                break;
        }
    }
}

// Helper function for generating all factors using DFS
void Fac_dfs(int x, int y, vector<int> &ans, vector<pair<int, int>> &FacList)
{
    if (x == FacList.size())
    {
        ans.push_back(y);
        return;
    }

    int k = 1;
    for (int i = 0; i <= FacList[x].second; ++i)
    {
        Fac_dfs(x + 1, y * k, ans, FacList);
        k *= FacList[x].first;
    }
}

// Function to get prime factorization of a number
vector<pair<int, int>> GetPrimeFac(int a)
{
    vector<pair<int, int>> answer;

    if (check_Prime[a])
        return {pair<int, int>{a, 1}};

    answer.push_back({OneFac[a], 1});
    a /= OneFac[a];

    while (!check_Prime[a])
    {
        if (OneFac[a] == answer.back().first)
            answer.back().second++;
        else
            answer.push_back({OneFac[a], 1});

        a /= OneFac[a];
    }

    if (a == answer.back().first)
        answer.back().second++;
    else
        answer.push_back({a, 1});

    return answer;
}
// Function to get all factors of a number
vector<int> GetFacList(int a)
{
    vector<int> ans;
    vector<std::pair<int, int>> FacList = GetPrimeFac(a);
    Fac_dfs(0, 1, ans, FacList);
    return ans;
}
// Initialize with a specific limit
void init(int n=10000005)
{
    check_Prime.resize(n + 2);
    OneFac.resize(n + 2);
    GetPrime(n);
}

vector<bool> sieve(int n)
{
    vector<bool> is_prime(n + 1, true);
    is_prime[0] = is_prime[1] = false;

    for (int i = 2; i * i <= n; ++i)
    {
        if (is_prime[i])
        {
            for (int j = i * i; j <= n; j += i)
            {
                is_prime[j] = false;
            }
        }
    }

    return is_prime;
}
long long fibonacci(int N)
{
    long long A = 1, B = 1;
    for (int i = 3; i <= N; i++)
    {
        long long temp = (A + B) % mod;
        A = B;
        B = temp;
    }
    return B;
}
bool prime(int x)
{
    for (int i = 2; i * i <= x; i++)
    {
        if (x % i == 0)
        {
            return 0;
        }
    }
    return 1;
}
int gcd(int a, int b)
{
    if (b == 0)
        return a;
    return gcd(b, a % b);
}
ll lcm(ll a, ll b) { return a / gcd(a, b) * b; }
int lcm(int a[], int n)
{
    int r = a[0];
    for (int i = 1; i < n; i++)
    {
        r = ((a[i] * r) / gcd(a[i], r));
    }
    return r;
}
ll binary_multiply(ll a, ll b) // we will use this only when mod is greater than 10^9. if mod is not >10^9 then don't use this in binary_exponentation.
{
    a %= mod;
    ll ans = 0;
    while (b > 0)
    {
        if (b & 1)
        {
            ans += a;
            ans %= mod;
        }
        b >>= 1;
        a += a;
        a %= mod;
    }
    return ans;
}
// Fast modular exponentiation: computes (base^exp) % mod. for finding MMI
ll binexp(ll base, ll exp)
{
    base %= mod;
    ll ans = 1;
    while (exp > 0)
    {
        if (exp & 1)
        {
            ans = (ans * base) % mod; // binary_multiply(ans,a);
        }
        exp >>= 1;
        base = (base * base) % mod; // binary_multiply(a,a);
    }
    return ans;
}
int fact(int m)
{
    if (m == 0 or m == 1)
    {
        return 1;
    }
    else
    {
        return m * fact(m - 1);
    }
}
int set_bits(int h)
{
    int c = 0;
    while (h)
    {
        c += (h & 1);
        h >>= 1;
    }
    return c;
}
int divisor(int n)
{
    // smallest divisor
    for (int i = 2; i < sqrt(n); i++)
    {
        if (n % i == 0)
            return i;
    }
    return -1;
}
bool isPrime(int n)
{
    if (n <= 1)
        return false;
    if (n == 2)
        return true;
    if (n % 2 == 0)
        return false;
    for (int i = 3; i * i <= n; i += 2)
    {
        if (n % i == 0)
            return false;
    }
    return true;
}
void swap(int &a, int &b)
{
    int temp = a;
    a = b;
    b = temp;
}
// adjacency list
void bfs(int node, vector<int> adj[], vector<int> &vis, vector<int> &ans)
{
    queue<int> q;
    q.push(node);
    vis[node] = 1;
    while (!q.empty())
    {
        int curr = q.front();
        q.pop();
        ans.push_back(curr);
        for (int neighbor : adj[curr])
        {
            if (!vis[neighbor])
            {
                vis[neighbor] = 1;
                q.push(neighbor);
            }
        }
    }
}

void dfs(int node, vector<int> adj[], vector<int> &vis, vector<int> &ans)
{
    vis[node] = 1;
    ans.push_back(node);
    for (int neighbor : adj[node])
    {
        if (!vis[neighbor])
        {
            dfs(neighbor, adj, vis, ans);
        }
    }
}
// matrix
void dfs(int row, int col, vector<vector<int>> &grid, vector<vector<bool>> &vis)
{
    int n = grid.size();
    int m = grid[0].size();
    vector<int> delRow = {-1, 0, 1, 0};
    vector<int> delCol = {0, 1, 0, -1};
    vis[row][col] = true;
    for (int i = 0; i < 4; i++)
    {
        int newRow = row + delRow[i];
        int newCol = col + delCol[i];
        if (newRow >= 0 && newRow < n && newCol >= 0 && newCol < m &&
            grid[newRow][newCol] == 1 && !vis[newRow][newCol])
        {
            dfs(newRow, newCol, grid, vis);
        }
    }
}
vector<int> traverseGraph(int V, vector<int> adj[])
{
    vector<int> vis(V, 0), ans;
    for (int i = 0; i < V; i++)
    {
        if (!vis[i])
        {
            bfs(i, adj, vis, ans);
            // dfs(i, adj, vis, ans); // uncomment this line to perform dfs
        }
    }
    return ans;
}

int countComponents(int V, vector<vector<int>> &edges)
{
    vector<int> adj[V], vis(V, 0);
    for (const auto &edge : edges)
    {
        adj[edge[0]].push_back(edge[1]);
        adj[edge[1]].push_back(edge[0]);
    }
    int components = 0;
    vi ans;
    for (int i = 0; i < V; i++)
    {
        if (!vis[i])
        {
            components++;
            bfs(i, adj, vis, ans);
        }
    }
    return components;
}

// Disjoint Set Union (DSU)
class DisjointSet {
public:
    vector<int> parent, size, rank;

    DisjointSet(int n) {
        parent.resize(n);
        size.resize(n, 1);  
        rank.resize(n, 0); 
        for (int i = 0; i < n; i++) {
            parent[i] = i;
        }
    }

    int findpar(int node) {
        if (node == parent[node])
            return node;
        return parent[node] = findpar(parent[node]); 
    }

    void unionr(int u, int v) {
        int pu = findpar(u);
        int pv = findpar(v);
        if (pu == pv) return;

        if (rank[pu] < rank[pv]) {
            parent[pu] = pv;
        } else if (rank[pv] < rank[pu]) {
            parent[pv] = pu;
        } else {
            parent[pv] = pu;
            rank[pu]++;
        }
    }

    void unions(int u, int v) {
        int pu = findpar(u);
        int pv = findpar(v);
        if (pu == pv) return;

        if (size[pu] < size[pv]) {
            parent[pu] = pv;
            size[pv] += size[pu];
        } else {
            parent[pv] = pu;
            size[pu] += size[pv];
        }
    }
};

void solveQuery(vi v, int a, int b)
{
}
void queries()
{
    int n, q;
    cin >> n >> q;
    vi v(n);
    for (int &t : v)
        cin >> t;

    while (q--)
    {
        int a, b;
        cin >> a >> b;
        solveQuery(v, a, b);
    }
}
void solve(int test)
{

}
int32_t main()
{
    ios;
    int test=1;
    int t;cin >> t;
    if (test) while (t--) solve(test++);
    else solve(test);
    // cout<<"SupreethC";
    // Queries
    // queries();
    return 0;
}
