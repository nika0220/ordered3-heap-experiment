#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <random>
#include <stdexcept>
#include <vector>

struct CountStats {
    std::uint64_t comparisons = 0;
    std::uint64_t build_comparisons = 0;
    std::uint64_t pop_comparisons = 0;
    std::uint64_t subtree_swaps = 0;
    std::uint64_t value_swaps = 0;
    std::uint64_t hole_steps = 0;
    std::uint64_t generic_hole_steps = 0;
};

static bool is_perfect_tree_size(std::size_t n) {
    return n != 0 && ((n + 1) & n) == 0;
}

static std::size_t left_child(std::size_t i) { return i * 2 + 1; }
static std::size_t right_child(std::size_t i) { return i * 2 + 2; }

template <class T, class Less>
static bool counted_less_build(const T& a, const T& b, Less less, CountStats& st) {
    ++st.comparisons;
    ++st.build_comparisons;
    return less(a, b);
}

template <class T, class Less>
static bool counted_less_pop(const T& a, const T& b, Less less, CountStats& st) {
    ++st.comparisons;
    ++st.pop_comparisons;
    return less(a, b);
}

template <class T>
static void swap_subtree_values(std::vector<T>& heap, std::size_t a, std::size_t b, CountStats& st) {
    const std::size_t n = heap.size();
    if (a >= n || b >= n) return;
    std::swap(heap[a], heap[b]);
    ++st.value_swaps;
    ++st.subtree_swaps;
    swap_subtree_values(heap, left_child(a), left_child(b), st);
    swap_subtree_values(heap, right_child(a), right_child(b), st);
}

template <class T, class Less>
static bool check_ordered3_full(const std::vector<T>& heap, Less less) {
    const std::size_t n = heap.size();
    for (std::size_t i = 0; i < n; ++i) {
        const std::size_t L = left_child(i);
        const std::size_t R = right_child(i);
        if (L < n && less(heap[i], heap[L])) return false;
        if (R < n) {
            if (less(heap[i], heap[R])) return false;
            if (less(heap[L], heap[R])) return false;
        }
    }
    return true;
}

template <class T, class Less>
static bool check_ordered3_alive_relaxed(const std::vector<T>& heap,
                                         const std::vector<unsigned char>& alive,
                                         Less less) {
    const std::size_t n = heap.size();
    for (std::size_t i = 0; i < n; ++i) {
        const std::size_t L = left_child(i);
        const std::size_t R = right_child(i);
        if (L < n && alive[L]) {
            if (!alive[i]) return false;
            if (less(heap[i], heap[L])) return false;
        }
        if (R < n && alive[R]) {
            if (!alive[i]) return false;
            if (less(heap[i], heap[R])) return false;
            if (L < n && alive[L] && less(heap[L], heap[R])) return false;
        }
    }
    return true;
}


template <class T, class Less>
static bool check_ordered3_alive_strict(const std::vector<T>& heap,
                                        const std::vector<unsigned char>& alive,
                                        Less less) {
    const std::size_t n = heap.size();
    for (std::size_t i = 0; i < n; ++i) {
        const std::size_t L = left_child(i);
        const std::size_t R = right_child(i);
        const bool hasL = (L < n && alive[L]);
        const bool hasR = (R < n && alive[R]);
        if ((hasL || hasR) && !alive[i]) return false;
        if (hasR && !hasL) return false; // no right-only live child in strict ordered3.
        if (hasL && less(heap[i], heap[L])) return false;
        if (hasR) {
            if (less(heap[i], heap[R])) return false;
            if (less(heap[L], heap[R])) return false;
        }
    }
    return true;
}

template <class T, class Less>
static void post_fix_sibling_build(std::vector<T>& heap,
                                   std::size_t p,
                                   Less less,
                                   CountStats& st) {
    const std::size_t n = heap.size();
    const std::size_t l = left_child(p);
    const std::size_t r = right_child(p);
    if (r < n && counted_less_build(heap[l], heap[r], less, st)) {
        swap_subtree_values(heap, l, r, st);
    }
}

// Repair when child subtrees are ordered and left root >= right root is known.
// New "always go left" repair requested by user:
//   if P >= L: stop
//   else swap P,L; repair the changed left branch; then if R > newL, subtree-swap L/R.
template <class T, class Less>
static void repair_known_child_order_build(std::vector<T>& heap,
                                           std::size_t p,
                                           Less less,
                                           CountStats& st) {
    const std::size_t n = heap.size();
    if (p >= n) return;
    const std::size_t l = left_child(p);
    if (l >= n) return;

    const std::size_t r = l + 1;
    // With only one child, ordinary sift-down.
    if (r >= n) {
        if (counted_less_build(heap[p], heap[l], less, st)) {
            std::swap(heap[p], heap[l]);
            ++st.value_swaps;
            repair_known_child_order_build(heap, l, less, st);
        }
        return;
    }

    // Known before entering: heap[l] >= heap[r]. Do not compare L/R.
    if (!counted_less_build(heap[p], heap[l], less, st)) {
        return; // P >= L >= R
    }

    // L > P. Move L up, push P into left branch, repair that branch.
    std::swap(heap[p], heap[l]);
    ++st.value_swaps;
    repair_known_child_order_build(heap, l, less, st);

    // Now local shape is [old L, new_left_root, R].
    // Since old L >= R is known, only left/right order may be wrong.
    if (counted_less_build(heap[l], heap[r], less, st)) {
        swap_subtree_values(heap, l, r, st);
    }
}

template <class T, class Less>
static void build_step_known_child_order(std::vector<T>& heap,
                                         std::size_t p,
                                         Less less,
                                         CountStats& st) {
    const std::size_t n = heap.size();
    const std::size_t l = left_child(p);
    if (l >= n) return;

    const std::size_t r = l + 1;
    if (r >= n) {
        if (counted_less_build(heap[p], heap[l], less, st)) {
            std::swap(heap[p], heap[l]);
            ++st.value_swaps;
            repair_known_child_order_build(heap, l, less, st);
        }
        return;
    }

    // First make child roots ordered: L >= R. This is the 2/3/6 subtree-swap entry.
    if (counted_less_build(heap[l], heap[r], less, st)) {
        swap_subtree_values(heap, l, r, st);
    }

    // Now L >= R is known, so use the simple repair.
    repair_known_child_order_build(heap, p, less, st);
}

template <class T, class Less>
static CountStats build_ordered3_user_physical(std::vector<T>& heap, Less less) {
    CountStats st;
    const std::size_t n = heap.size();
    if (!is_perfect_tree_size(n)) {
        throw std::runtime_error("ordered3 known-order build expects n = 2^h - 1");
    }
    if (n <= 1) return st;

    for (std::size_t node = n / 2; node > 0; --node) {
        build_step_known_child_order(heap, node - 1, less, st);
    }
#ifndef NDEBUG
    if (!check_ordered3_full(heap, less)) {
        throw std::runtime_error("ordered3 known-order build produced broken invariant");
    }
#endif
    return st;
}




// Build repair variant: insert P into the already-ordered left spine by binary search,
// shift the left-spine values upward, then fix sibling order only on the changed spine range.
template <class T, class Less>
static void repair_known_child_order_build_spine_insert(std::vector<T>& heap,
                                                        std::size_t p,
                                                        Less less,
                                                        CountStats& st) {
    const std::size_t n = heap.size();
    if (p >= n) return;
    const std::size_t l0 = left_child(p);
    if (l0 >= n) return;

    // Collect p, left(p), left(left(p)), ... .
    std::vector<std::size_t> spine;
    for (std::size_t v = p; v < n; v = left_child(v)) {
        spine.push_back(v);
        if (left_child(v) >= n) break;
    }

    const std::size_t m = spine.size() - 1; // number of left-spine descendants
    if (m == 0) return;

    const T probe = heap[p];

    // Find insertion position in descending sequence heap[spine[1]],...,heap[spine[m]].
    // pos=0 means P >= first left child, so no repair is needed.
    std::size_t lo = 0, hi = m;
    while (lo < hi) {
        const std::size_t mid = (lo + hi) / 2;
        const T& x = heap[spine[1 + mid]];
        if (counted_less_build(probe, x, less, st)) {
            // probe < x, so it must go below this left-spine value.
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    const std::size_t pos = lo;
    if (pos == 0) return;

    // Shift values upward along spine[0..pos], insert old P at spine[pos].
    T tmp = std::move(heap[spine[0]]);
    for (std::size_t i = 0; i < pos; ++i) {
        heap[spine[i]] = std::move(heap[spine[i + 1]]);
        ++st.value_swaps;
    }
    heap[spine[pos]] = std::move(tmp);
    ++st.value_swaps;

    // Fix sibling order for the changed part, including inserted node, bottom-up.
    for (std::size_t ii = pos + 1; ii > 0; --ii) {
        const std::size_t node = spine[ii - 1];
        const std::size_t l = left_child(node);
        const std::size_t r = l + 1;
        if (r < n && counted_less_build(heap[l], heap[r], less, st)) {
            swap_subtree_values(heap, l, r, st);
        }
    }
}

template <class T, class Less>
static void build_step_spine_insert(std::vector<T>& heap,
                                    std::size_t p,
                                    Less less,
                                    CountStats& st) {
    const std::size_t n = heap.size();
    const std::size_t l = left_child(p);
    if (l >= n) return;
    const std::size_t r = l + 1;
    if (r >= n) {
        // Complete-tree experiments do not normally hit this branch, but keep it safe.
        if (counted_less_build(heap[p], heap[l], less, st)) {
            std::swap(heap[p], heap[l]);
            ++st.value_swaps;
            repair_known_child_order_build_spine_insert(heap, l, less, st);
        }
        return;
    }

    // First make child roots ordered: L >= R.
    if (counted_less_build(heap[l], heap[r], less, st)) {
        swap_subtree_values(heap, l, r, st);
    }

    // Then repair by binary insertion into the left spine.
    repair_known_child_order_build_spine_insert(heap, p, less, st);
}

template <class T, class Less>
static CountStats build_ordered3_spine_insert_physical(std::vector<T>& heap, Less less) {
    CountStats st;
    const std::size_t n = heap.size();
    if (!is_perfect_tree_size(n)) {
        throw std::runtime_error("ordered3 spine-insert build expects n = 2^h - 1");
    }
    if (n <= 1) return st;

    for (std::size_t node = n / 2; node > 0; --node) {
        build_step_spine_insert(heap, node - 1, less, st);
    }
#ifndef NDEBUG
    if (!check_ordered3_full(heap, less)) {
        throw std::runtime_error("ordered3 spine-insert build produced broken invariant");
    }
#endif
    return st;
}


template <class T, class Less>
static void repair_hole_left_child_sibling_strict(std::vector<T>& heap,
                                                  std::vector<unsigned char>& alive,
                                                  std::size_t hole,
                                                  Less less,
                                                  CountStats& st);

template <class T, class Less>
static void repair_hole_right_child_strict(std::vector<T>& heap,
                                           std::vector<unsigned char>& alive,
                                           std::size_t hole,
                                           Less less,
                                           CountStats& st) {
    const std::size_t n = heap.size();
    if (hole >= n) return;

    ++st.hole_steps;
    const std::size_t A = left_child(hole);
    if (A < n && alive[A]) {
        // The right-hole subtree is ordered, so its left root is its maximum.
        heap[hole] = std::move(heap[A]);
        alive[hole] = 1;
        alive[A] = 0;
        // The new hole is a left child. Continue with the sibling-aware repair.
        repair_hole_left_child_sibling_strict(heap, alive, A, less, st);
    } else {
        // No live children under this right-hole node.
        alive[hole] = 0;
    }
}

template <class T, class Less>
static void repair_hole_left_child_sibling_strict(std::vector<T>& heap,
                                                  std::vector<unsigned char>& alive,
                                                  std::size_t hole,
                                                  Less less,
                                                  CountStats& st) {
    const std::size_t n = heap.size();

    while (hole < n) {
        ++st.hole_steps;
        const std::size_t S = hole + 1;          // right sibling of this left-hole position
        const std::size_t A = left_child(hole);  // max candidate of the hole subtree

        const bool hasA = (A < n && alive[A]);
        const bool hasS = (S < n && alive[S]);

        if (!hasA) {
            if (hasS) {
                heap[hole] = std::move(heap[S]);
                alive[hole] = 1;
                alive[S] = 0;
                // S may still have live descendants; repair this right-child hole strictly.
                repair_hole_right_child_strict(heap, alive, S, less, st);
            }
            return;
        }

        if (!hasS) {
            heap[hole] = std::move(heap[A]);
            alive[hole] = 1;
            alive[A] = 0;
            hole = A;
            continue;
        }

        // Before: [P, hole, S, A, B, A', B']
        // If A >= S: [P, A, S, hole, B, A', B']
        // If S > A:  [P, S, A', A, B, hole, B']
        if (counted_less_pop(heap[A], heap[S], less, st)) { // S > A
            heap[hole] = std::move(heap[S]);
            alive[hole] = 1;

            const std::size_t Ap = left_child(S); // A'
            if (Ap < n && alive[Ap]) {
                heap[S] = std::move(heap[Ap]);
                alive[S] = 1;
                alive[Ap] = 0;
                hole = Ap; // still a left-child hole
            } else {
                alive[S] = 0;
                // S has no live descendants, so the right leaf hole is finished.
                return;
            }
        } else { // A >= S
            heap[hole] = std::move(heap[A]);
            alive[hole] = 1;
            alive[A] = 0;
            hole = A; // still a left-child hole
        }
    }
}

template <class T, class Less = std::less<T>>
static CountStats sort_ordered3_hole_physical(std::vector<T>& values, Less less = Less{}) {
    CountStats st;
    const std::size_t n = values.size();
    if (n <= 1) return st;
    if (!is_perfect_tree_size(n)) {
        throw std::runtime_error("ordered3 strict-hole physical sort expects n = 2^h - 1");
    }

    st = build_ordered3_user_physical(values, less);

    std::vector<unsigned char> alive(n, 1);
    std::vector<T> descending;
    descending.reserve(n);

    for (std::size_t out = 0; out < n; ++out) {
        if (!alive[0]) throw std::runtime_error("ordered3 lost root");
        descending.push_back(std::move(values[0]));
        alive[0] = 0;

        const std::size_t L = 1;
        const bool hasL = (L < n && alive[L]);
        if (hasL) {
            // In strict ordered3, root's left child is always >= right child.
            // Do not compare L/R here; always promote L and repair the left hole.
            values[0] = std::move(values[L]);
            alive[0] = 1;
            alive[L] = 0;
            repair_hole_left_child_sibling_strict(values, alive, L, less, st);
        }

#ifndef NDEBUG
        if (!check_ordered3_alive_strict(values, alive, less)) {
            throw std::runtime_error("ordered3 strict invariant broken after pop");
        }
#endif
    }

    values.assign(descending.rbegin(), descending.rend());
    return st;
}


template <class T, class Less = std::less<T>>
static CountStats sort_ordered3_spinebuild_hole_physical(std::vector<T>& values, Less less = Less{}) {
    CountStats st;
    const std::size_t n = values.size();
    if (n <= 1) return st;
    if (!is_perfect_tree_size(n)) {
        throw std::runtime_error("ordered3 spine-build strict-hole physical sort expects n = 2^h - 1");
    }

    st = build_ordered3_spine_insert_physical(values, less);

    std::vector<unsigned char> alive(n, 1);
    std::vector<T> descending;
    descending.reserve(n);

    for (std::size_t out = 0; out < n; ++out) {
        if (!alive[0]) throw std::runtime_error("ordered3 spine-build lost root");
        descending.push_back(std::move(values[0]));
        alive[0] = 0;

        const std::size_t L = 1;
        const bool hasL = (L < n && alive[L]);
        if (hasL) {
            values[0] = std::move(values[L]);
            alive[0] = 1;
            alive[L] = 0;
            repair_hole_left_child_sibling_strict(values, alive, L, less, st);
        }

#ifndef NDEBUG
        if (!check_ordered3_alive_strict(values, alive, less)) {
            throw std::runtime_error("ordered3 spine-build strict invariant broken after pop");
        }
#endif
    }

    values.assign(descending.rbegin(), descending.rend());
    return st;
}


template <class T, class Less = std::less<T>>
static CountStats sort_binary_heap_count(std::vector<T>& values, Less less = Less{}) {
    CountStats st;
    const std::size_t n = values.size();
    if (n <= 1) return st;

    auto less_count = [&](const T& a, const T& b) {
        ++st.comparisons;
        return less(a, b);
    };

    auto sift_down = [&](std::size_t node, std::size_t size) {
        while (true) {
            const std::size_t L = left_child(node);
            if (L >= size) return;
            const std::size_t R = L + 1;
            std::size_t child = L;
            if (R < size && less_count(values[L], values[R])) child = R;
            if (!less_count(values[node], values[child])) return;
            std::swap(values[node], values[child]);
            ++st.value_swaps;
            node = child;
        }
    };

    for (std::size_t node = n / 2; node > 0; --node) sift_down(node - 1, n);
    for (std::size_t size = n; size > 1; --size) {
        std::swap(values[0], values[size - 1]);
        ++st.value_swaps;
        sift_down(0, size - 1);
    }
    return st;
}



template <class T, class Less = std::less<T>>
static CountStats sort_weak_heap_count(std::vector<T>& values, Less less = Less{}) {
    CountStats st;
    const std::size_t n = values.size();
    if (n <= 1) return st;

    std::vector<unsigned char> reverse(n, 0);

    auto less_count_build = [&](const T& a, const T& b) {
        ++st.comparisons;
        ++st.build_comparisons;
        return less(a, b);
    };
    auto less_count_pop = [&](const T& a, const T& b) {
        ++st.comparisons;
        ++st.pop_comparisons;
        return less(a, b);
    };

    auto distinguished_ancestor = [&](std::size_t j) {
        std::size_t i = j >> 1;
        while (i > 0 && ((j & 1u) == static_cast<std::size_t>(reverse[i]))) {
            j = i;
            i >>= 1;
        }
        return i;
    };

    auto join_build = [&](std::size_t i, std::size_t j) {
        // Max weak heap join. If child root wins, swap it to ancestor and flip j.
        if (less_count_build(values[i], values[j])) {
            std::swap(values[i], values[j]);
            reverse[j] ^= 1u;
            ++st.value_swaps;
            return true;
        }
        return false;
    };

    auto join_pop = [&](std::size_t i, std::size_t j) {
        if (less_count_pop(values[i], values[j])) {
            std::swap(values[i], values[j]);
            reverse[j] ^= 1u;
            ++st.value_swaps;
            return true;
        }
        return false;
    };

    // Build weak heap. Exactly n-1 joins/comparisons.
    for (std::size_t j = n - 1; j > 0; --j) {
        join_build(distinguished_ancestor(j), j);
    }

    // Repeatedly move the maximum to the end, then repair the weak heap on [0, m).
    for (std::size_t m = n - 1; m > 1; --m) {
        std::swap(values[0], values[m]);
        ++st.value_swaps;

        // Follow distinguished-child links down to the bottom of the remaining weak heap.
        std::size_t x = 1;
        while ((2 * x + static_cast<std::size_t>(reverse[x])) < m) {
            x = 2 * x + static_cast<std::size_t>(reverse[x]);
        }

        // Join the root with the nodes on the way back up.
        while (x > 0) {
            join_pop(0, x);
            x >>= 1;
        }
    }

    if (n > 1) {
        // Final two elements.
        if (less_count_pop(values[1], values[0])) {
            std::swap(values[0], values[1]);
            ++st.value_swaps;
        }
    }
    return st;
}

template <class T>
static bool is_sorted_asc(const std::vector<T>& a) {
    return std::is_sorted(a.begin(), a.end());
}

static std::vector<int> random_vec(std::size_t n, std::mt19937& rng) {
    std::vector<int> v(n);
    for (std::size_t i = 0; i < n; ++i) v[i] = static_cast<int>(i + 1);
    std::shuffle(v.begin(), v.end(), rng);
    return v;
}


#include <cmath>
#include <iomanip>
#include <numeric>

static long double log2_factorial_ld(std::size_t n) {
    long double s = 0.0L;
    for (std::size_t i = 2; i <= n; ++i) s += std::log2((long double)i);
    return s;
}

static void exact_permutation_test(std::size_t n) {
    std::vector<int> base(n);
    std::iota(base.begin(), base.end(), 1);
    unsigned long long count = 0;
    unsigned long long o_sum=0, w_sum=0, b_sum=0;
    unsigned long long o_max=0, w_max=0, b_max=0;
    unsigned long long o_min=~0ull, w_min=~0ull, b_min=~0ull;
    do {
        auto a=base; auto so=sort_ordered3_hole_physical(a); if(!is_sorted_asc(a)) throw std::runtime_error("ordered exact failed");
        auto w=base; auto sw=sort_weak_heap_count(w); if(!is_sorted_asc(w)) throw std::runtime_error("weak exact failed");
        auto b=base; auto sb=sort_binary_heap_count(b); if(!is_sorted_asc(b)) throw std::runtime_error("binary exact failed");
        ++count;
        o_sum += so.comparisons; w_sum += sw.comparisons; b_sum += sb.comparisons;
        o_max = std::max<unsigned long long>(o_max, so.comparisons);
        w_max = std::max<unsigned long long>(w_max, sw.comparisons);
        b_max = std::max<unsigned long long>(b_max, sb.comparisons);
        o_min = std::min<unsigned long long>(o_min, so.comparisons);
        w_min = std::min<unsigned long long>(w_min, sw.comparisons);
        b_min = std::min<unsigned long long>(b_min, sb.comparisons);
    } while(std::next_permutation(base.begin(), base.end()));
    std::cout << "EXACT n=" << n
              << " perms=" << count
              << " ordered_avg=" << (long double)o_sum/count
              << " ordered_min=" << o_min << " ordered_max=" << o_max
              << " weak_avg=" << (long double)w_sum/count
              << " weak_min=" << w_min << " weak_max=" << w_max
              << " binary_avg=" << (long double)b_sum/count
              << " binary_min=" << b_min << " binary_max=" << b_max
              << "\n";
}


int main() {
    using clock = std::chrono::steady_clock;
    std::cout << std::fixed << std::setprecision(6);
    std::mt19937 rng(1234567);

    std::cout << "SPINE INSERT BUILD EXPERIMENT\n";
    std::cout << "Compare original always-left build vs spine-binary-insert build; same strict pop.\n\n";
    std::cout << "n,reps,orig_total,orig_build,orig_pop,spine_total,spine_build,spine_pop,weak_total,binary_total,spine_minus_orig,spine_build_minus_orig_build,sorted\n";

    for (std::size_t n : {15u,31u,63u,127u,255u,511u,1023u,2047u,4095u,8191u,16383u,32767u,65535u,131071u,262143u,524287u}) {
        int reps;
        if (n <= 1023) reps = 200;
        else if (n <= 8191) reps = 80;
        else if (n <= 32767) reps = 30;
        else if (n <= 131071) reps = 10;
        else reps = 3;

        long double orig_total=0, orig_build=0, orig_pop=0;
        long double spine_total=0, spine_build=0, spine_pop=0;
        long double weak_total=0, binary_total=0;
        bool ok=true;

        for(int rep=0; rep<reps; ++rep) {
            auto base=random_vec(n,rng);

            auto a=base;
            auto so=sort_ordered3_hole_physical(a);
            ok = ok && is_sorted_asc(a);
            orig_total += so.comparisons;
            orig_build += so.build_comparisons;
            orig_pop += so.pop_comparisons;

            auto s=base;
            auto ss=sort_ordered3_spinebuild_hole_physical(s);
            ok = ok && is_sorted_asc(s);
            spine_total += ss.comparisons;
            spine_build += ss.build_comparisons;
            spine_pop += ss.pop_comparisons;

            auto w=base;
            auto sw=sort_weak_heap_count(w);
            ok = ok && is_sorted_asc(w);
            weak_total += sw.comparisons;

            auto b=base;
            auto sb=sort_binary_heap_count(b);
            ok = ok && is_sorted_asc(b);
            binary_total += sb.comparisons;
        }
        orig_total/=reps; orig_build/=reps; orig_pop/=reps;
        spine_total/=reps; spine_build/=reps; spine_pop/=reps;
        weak_total/=reps; binary_total/=reps;

        std::cout << n << "," << reps
                  << "," << orig_total
                  << "," << orig_build
                  << "," << orig_pop
                  << "," << spine_total
                  << "," << spine_build
                  << "," << spine_pop
                  << "," << weak_total
                  << "," << binary_total
                  << "," << (spine_total - orig_total)
                  << "," << (spine_build - orig_build)
                  << "," << ok
                  << "\n";
    }
    return 0;
}
