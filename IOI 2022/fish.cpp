#include <iostream>
#include <vector>
#include <algorithm>
#include <map>
#include <array>
// #include <assert.h>
#include <deque>

using namespace std;
#define assert(X) {}

class NoOutput : public std::basic_ostream<char> {

};

template<class V>
NoOutput& operator<<(NoOutput& os, const V& v) {
	return os;
}
// NoOutput err;
// ostream& err = cerr;

typedef long long int64 ;
const int64 INF = 1e15L;
const int MAXN = 100000+10;

bool is_sorted(const vector<int>& v) {
	for (size_t i=1; i<v.size(); i++) {
		if (v[i-1] > v[i]) return false;
	}
	return true;
}

// return first index i such that k<=v[i], if not returns v.size()
int lowest_geq(const vector<int>& v, int k) {
	auto it = lower_bound(v.begin(), v.end(), k);
	return it == v.end() ? (int) v.size() : it - v.begin();
}

vector<pair<int,int>> transform_container(const vector<int>& c, std::function<pair<int,int> (int)> &&f) {
    vector<pair<int,int>> ret;
    std::transform(std::begin(c), std::end(c), std::inserter(ret, std::end(ret)), f);
    return ret;
}

template<typename T>
ostream& operator<<(ostream& os, const vector<T>& v) {
	os << "[";
	for (auto const& vv: v) 
		os << vv << " ";
	return os << "]";
}

template<typename T>
ostream& operator<<(ostream& os, const deque<T>& v) {
	os << "[";
	for (auto const& vv: v) 
		os << vv << " ";
	return os << "]";
}


template<typename T, typename C>
ostream& operator<<(ostream& os, const pair<T, C>& v) {
	return os << v.first << ":" << v.second;
}

struct IntervalTree {
	int n;
	vector<int64> t; 
	vector<int> key;

	void build(const vector<pair<int,int>> key_value) {
		n = key_value.size();
		t.resize(2*n);
		key.clear();
		for (size_t i=0; i<key_value.size(); i++) {
			key.push_back(key_value[i].first);
			t[n+i] = key_value[i].second;
		}
		assert(is_sorted(key));
		for (int i = n - 1; i > 0; --i) t[i] = t[i<<1] + t[i<<1|1];
	}

	int get_index(int p) const {
		return t[p+n];
	}

	void set_index(int p, int value) {
		for (t[p += n] = value; p > 1; p >>= 1) t[p>>1] = t[p] + t[p^1];
	}

	int64 query_index(int l, int r) const {  // sum on interval [l, r)
		int64 res = 0;
		for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
			if (l&1) res += t[l++];
			if (r&1) res += t[--r];
		}
		return res;
	}

	int lowest_geq_index(int v) const {
		return lowest_geq(key, v);
	}

	int64 query(int l_v, int r_v) const {
		return query_index(lowest_geq(key, l_v), lowest_geq(key, r_v));
	}

};


// sum of weight of fishes in column i in rows [x-y)
int64 fish(const IntervalTree & tree, int x, int y) {
	return tree.query(x, y);
}

int N;
map<int, int64> dp_iminus1_down, dp_iminus1_up;
// , dp_i_down, dp_i_up;

// max_{N>=y >= x} DP[i-1,y,down] + fish(i,[x-y)), DP[i-1,y,up] + fish(i,[x-y))
int64 max_1(const IntervalTree& tree_i, int x) {
	//naive
	int64 res = 0;
	for (int y = x; y <= N; y++) {
		// err << "max_1(" << x << ") " << (dp_iminus1_down.find(y) != dp_iminus1_down.end() ? dp_iminus1_down[y] : -INF) << " " << (dp_iminus1_up.find(y) != dp_iminus1_up.end() ? dp_iminus1_up[y] : -INF) << " " << fish(tree_i, x, y) << endl;
		res = max(res, max(
			dp_iminus1_down.find(y) != dp_iminus1_down.end() ? 
				dp_iminus1_down[y] : -INF, 
			dp_iminus1_up.find(y) != dp_iminus1_up.end() ? 
				dp_iminus1_up[y] : -INF) + fish(tree_i, x, y));
	}
	return res;
}

// max_{0<=y<= x} DP[i-1,y,up] + fish(i-1,[y-x))
int64 max_2(const IntervalTree& tree_iminus1, int x) {
	//naive
	int64 res = 0;
	for (int y = 0; y <= x; y++) {
		// err << "max_2(" << x << ") " << (dp_iminus1_up.find(y) != dp_iminus1_up.end() ? dp_iminus1_up[y] : -INF) << " " << fish(tree_iminus1, y, x) << endl;
		res = max(res, 
			(dp_iminus1_up.find(y) != dp_iminus1_up.end() ? 
				dp_iminus1_up[y] : -INF) + fish(tree_iminus1, y, x));
	}
	return res;
}

int64 max_weights(int N, int M, vector<int> X, vector<int> Y, vector<int> W) {
	::N = N;
	// err << "Input: X=" << X << " Y=" << Y << " W=" << W << endl;

	array<vector<int>, MAXN> column_fish_index;
	for (size_t f=0; f<(size_t)M; f++) {
		column_fish_index[X[f]].push_back(f);
	}

	for (size_t i=0; i<(size_t)N+1; i++) {
		sort(column_fish_index[i].begin(), 
			column_fish_index[i].end(), 
				[&](int f1, int f2) { return Y[f1] < Y[f2]; });
		// err << "column_fish_index[" << i << "]=" << column_fish_index[i] << endl;
	}

	IntervalTree tree_iminus1;
	tree_iminus1.build(transform_container(
		column_fish_index[0], 
		[&Y, &W](int f) { return make_pair(Y[f], W[f]); }));

	dp_iminus1_down = dp_iminus1_up = map<int, int64>();
	dp_iminus1_down[0] = dp_iminus1_up[0] = 0;
	for (size_t c=0; c<=1; c++) {
		for (auto f : column_fish_index[c]) {
			dp_iminus1_up[Y[f]+1] = 0;
		}
	}

	for (size_t i=1; i<(size_t)N+1; i++) {
		// err << "Column " << i << endl;
		vector<int> important_rows_i;
		important_rows_i.push_back(0);
		for (size_t c=i-1; c<=i+1; c++) {
			for (auto f : column_fish_index[c]) {
				important_rows_i.push_back(Y[f]+1);
			}
		}
		sort(important_rows_i.begin(), important_rows_i.end());
		// err << "important_rows_i: " << important_rows_i << endl;
		important_rows_i.resize(unique(important_rows_i.begin(), 
			important_rows_i.end()) - important_rows_i.begin());
		// err << "important_rows_i: " << important_rows_i << endl;
		
		//fill fish interval tree
		IntervalTree tree_i;
		tree_i.build(transform_container(column_fish_index[i], 
			[&Y, &W](int f) { return make_pair(Y[f], W[f]); }));

		// max_{N>=y >= x} DP[i-1,y,down] + fish(i,[x-y)), DP[i-1,y,up] + fish(i,[x-y))
		vector<pair<int,int64>> max_1_discrete;
		max_1_discrete.reserve(dp_iminus1_up.size() + 1);
		max_1_discrete.push_back(make_pair(N+1, -INF));
		for (map<int, int64>::reverse_iterator x = dp_iminus1_up.rbegin(); 
			x != dp_iminus1_up.rend(); x++) {
			auto prev = max_1_discrete.back();
			max_1_discrete.push_back(make_pair(x->first, 
				max(fish(tree_i, x->first, prev.first) + prev.second, 
					max(dp_iminus1_down[x->first], dp_iminus1_up[x->first])) 
			));
			// err << "max_1_discrete[" << x->first << "] p=" << prev << " a)" << (fish(tree_i, x->first, prev.first) + prev.second) << " b)" << dp_iminus1_down[x->first] << " c)" << dp_iminus1_up[x->first] << endl;
		}
		reverse(max_1_discrete.begin(), max_1_discrete.end());
		// err << "max_1_discrete: " << max_1_discrete << endl;

		vector<pair<int,int64>> max_2_discrete;
		max_2_discrete.reserve(dp_iminus1_up.size());
		// max_{0<=y<= x} DP[i-1,y,up] + fish(i-1,[y-x))
		for (auto const& x: dp_iminus1_up) {
			if (max_2_discrete.size() > 0) {
				auto prev = max_2_discrete.back();
				max_2_discrete.push_back(
					make_pair(
						x.first,
						max(
							fish(tree_iminus1, prev.first, x.first) + prev.second,
							dp_iminus1_up[x.first]
						)
					)
				);
			} else {
				max_2_discrete.push_back(
					make_pair(
						x.first,						
						dp_iminus1_up[x.first]
					)
				);
			}
		}
		// err << "max_2_discrete: " << max_2_discrete << endl;

		// dp_i_down = dp_i_up = map<int, int64>();
		vector<pair<int,int64>> dp_i_down, dp_i_up;
		for (auto x : important_rows_i) {
			// dp_i_down[x] = max_1(tree_i, x);
			auto max_1_discrete_it = lower_bound(max_1_discrete.begin(), 
				max_1_discrete.end(), x, 
				[](const pair<int, int64>& max_1_disc, int r) { return max_1_disc.first < r; });
			// err << "max_1_discrete_it: " << *max_1_discrete_it << endl;
			// dp_i_down[x] = 
			dp_i_down.push_back(make_pair(x,
				max_1_discrete_it == max_1_discrete.end() ? -INF : 
					max_1_discrete_it->second + fish(tree_i, x, max_1_discrete_it->first)
			));
			
			// dp_i_up[x] = max(max_2(tree_iminus1, x), dp_iminus1_down[0]);
			auto max_2_discrete_it = lower_bound(max_2_discrete.rbegin(), 
				max_2_discrete.rend(), x, 
				[](const pair<int, int64>& max_2_disc, int r) 
					{ return !(max_2_disc.first <= r); } );
			// err << "max_2_discrete_it: " << *max_2_discrete_it << " p=" << (max_2_discrete_it == max_2_discrete.rbegin() ? make_pair<int,int64>(-1,-1) : *prev(max_2_discrete_it)) << endl;
			assert(max_2_discrete_it->first <= x);
			assert(max_2_discrete_it == max_2_discrete.rbegin() || prev(max_2_discrete_it)->first > x);
			// dp_i_up[x] = 
			dp_i_up.push_back(make_pair(
				x, 
				max(max_2_discrete_it->second + 
						fish(tree_iminus1, max_2_discrete_it->first, x), 
					dp_iminus1_down[0])
			));
			// err << "dp[" << i << "," << x << "]=" << dp_i_down[x] << " ^:" << dp_i_up[x] << endl;
		}
		// dp_iminus1_down = dp_i_down;
		// dp_iminus1_up = dp_i_up;
		dp_iminus1_down = map<int,int64>(dp_i_down.begin(), dp_i_down.end());
		dp_iminus1_up = map<int,int64>(dp_i_up.begin(), dp_i_up.end());

		tree_iminus1 = tree_i;
	}
	return dp_iminus1_down[0];
}
