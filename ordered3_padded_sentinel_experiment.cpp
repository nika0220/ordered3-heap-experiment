#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <vector>

struct CountStats { uint64_t comparisons=0, build_comparisons=0, pop_comparisons=0, value_swaps=0, subtree_swaps=0, hole_steps=0; };
static std::size_t left_child(std::size_t i){ return i*2+1; }
static std::size_t right_child(std::size_t i){ return i*2+2; }
static bool is_perfect_tree_size(std::size_t n){ return n && (((n+1)&n)==0); }
static std::size_t next_perfect_size(std::size_t n){ std::size_t m=1; while(m<n) m=(m<<1)|1; return m; }

struct Node { int v=0; bool dummy=false; };
static bool node_less_raw(const Node& a, const Node& b){
    if(a.dummy && b.dummy) return false;
    if(a.dummy && !b.dummy) return true;
    if(!a.dummy && b.dummy) return false;
    return a.v < b.v;
}
static bool counted_less_build_node(const Node& a, const Node& b, CountStats& st){
    if(!a.dummy && !b.dummy){ ++st.comparisons; ++st.build_comparisons; }
    return node_less_raw(a,b);
}
static bool counted_less_pop_node(const Node& a, const Node& b, CountStats& st){
    if(!a.dummy && !b.dummy){ ++st.comparisons; ++st.pop_comparisons; }
    return node_less_raw(a,b);
}
static void swap_subtree_values(std::vector<Node>& heap, std::size_t a, std::size_t b, CountStats& st){
    const std::size_t n=heap.size(); if(a>=n||b>=n) return;
    std::swap(heap[a],heap[b]); ++st.value_swaps; ++st.subtree_swaps;
    swap_subtree_values(heap,left_child(a),left_child(b),st);
    swap_subtree_values(heap,right_child(a),right_child(b),st);
}
static bool check_ordered3_full(const std::vector<Node>& h){
    for(std::size_t i=0;i<h.size();++i){ auto L=left_child(i), R=right_child(i); if(L<h.size() && node_less_raw(h[i],h[L])) return false; if(R<h.size()){ if(node_less_raw(h[i],h[R])) return false; if(node_less_raw(h[L],h[R])) return false; } }
    return true;
}
static bool check_alive_strict(const std::vector<Node>& h, const std::vector<unsigned char>& alive){
    for(std::size_t i=0;i<h.size();++i){ auto L=left_child(i),R=right_child(i); bool hasL=L<h.size()&&alive[L]; bool hasR=R<h.size()&&alive[R]; if((hasL||hasR)&&!alive[i]) return false; if(hasR&&!hasL) return false; if(hasL&&node_less_raw(h[i],h[L])) return false; if(hasR){ if(node_less_raw(h[i],h[R])) return false; if(node_less_raw(h[L],h[R])) return false; } }
    return true;
}

static void repair_build_spine(std::vector<Node>& heap, std::size_t p, CountStats& st){
    const std::size_t n=heap.size(); if(p>=n) return; if(left_child(p)>=n) return;
    std::vector<std::size_t> spine; for(std::size_t v=p; v<n; v=left_child(v)){ spine.push_back(v); if(left_child(v)>=n) break; }
    const std::size_t m=spine.size()-1; if(m==0) return;
    Node probe=heap[p];
    std::size_t lo=0,hi=m;
    while(lo<hi){ std::size_t mid=(lo+hi)/2; const Node& x=heap[spine[1+mid]]; if(counted_less_build_node(probe,x,st)) lo=mid+1; else hi=mid; }
    std::size_t pos=lo; if(pos==0) return;
    Node tmp=std::move(heap[spine[0]]);
    for(std::size_t i=0;i<pos;++i){ heap[spine[i]]=std::move(heap[spine[i+1]]); ++st.value_swaps; }
    heap[spine[pos]]=std::move(tmp); ++st.value_swaps;
    for(std::size_t ii=pos+1; ii>0; --ii){ std::size_t node=spine[ii-1]; auto l=left_child(node), r=l+1; if(r<n && counted_less_build_node(heap[l],heap[r],st)) swap_subtree_values(heap,l,r,st); }
}
static void build_step(std::vector<Node>& heap, std::size_t p, CountStats& st){
    auto l=left_child(p); if(l>=heap.size()) return; auto r=l+1; if(r<heap.size() && counted_less_build_node(heap[l],heap[r],st)) swap_subtree_values(heap,l,r,st); repair_build_spine(heap,p,st);
}
static CountStats build_ordered3(std::vector<Node>& heap){
    CountStats st;
    for(std::size_t node=heap.size()/2; node>0; --node) build_step(heap,node-1,st);
#ifndef NDEBUG
    if(!check_ordered3_full(heap)) throw std::runtime_error("build bad");
#endif
    return st;
}

static void repair_left(std::vector<Node>& heap, std::vector<unsigned char>& alive, std::size_t hole, CountStats& st);
static void repair_right(std::vector<Node>& heap, std::vector<unsigned char>& alive, std::size_t hole, CountStats& st){
    if(hole>=heap.size()) return; ++st.hole_steps; auto A=left_child(hole); if(A<heap.size() && alive[A]){ heap[hole]=std::move(heap[A]); alive[hole]=1; alive[A]=0; repair_left(heap,alive,A,st); } else alive[hole]=0;
}
static void repair_left(std::vector<Node>& heap, std::vector<unsigned char>& alive, std::size_t hole, CountStats& st){
    const std::size_t n=heap.size();
    while(hole<n){ ++st.hole_steps; auto S=hole+1; auto A=left_child(hole); bool hasA=A<n&&alive[A]; bool hasS=S<n&&alive[S];
        if(!hasA){ if(hasS){ heap[hole]=std::move(heap[S]); alive[hole]=1; alive[S]=0; repair_right(heap,alive,S,st); } return; }
        if(!hasS){ heap[hole]=std::move(heap[A]); alive[hole]=1; alive[A]=0; hole=A; continue; }
        if(counted_less_pop_node(heap[A],heap[S],st)){ heap[hole]=std::move(heap[S]); alive[hole]=1; auto Ap=left_child(S); if(Ap<n&&alive[Ap]){ heap[S]=std::move(heap[Ap]); alive[S]=1; alive[Ap]=0; hole=Ap; } else { alive[S]=0; return; } }
        else { heap[hole]=std::move(heap[A]); alive[hole]=1; alive[A]=0; hole=A; }
    }
}

static CountStats sort_ordered3_padded(std::vector<int>& vals){
    const std::size_t n=vals.size(); if(n<=1) return {};
    const std::size_t m=next_perfect_size(n);
    std::vector<Node> heap(m);
    for(std::size_t i=0;i<n;++i) heap[i]={vals[i],false};
    for(std::size_t i=n;i<m;++i) heap[i]={0,true};
    CountStats st=build_ordered3(heap);
    std::vector<unsigned char> alive(m,1);
    std::vector<int> desc; desc.reserve(n);
    while(desc.size()<n){
        if(!alive[0]) throw std::runtime_error("lost root");
        if(heap[0].dummy) throw std::runtime_error("dummy root before all real");
        desc.push_back(heap[0].v);
        alive[0]=0;
        auto L=1u;
        if(L<m && alive[L]){
            heap[0]=std::move(heap[L]);
            alive[0]=1;
            alive[L]=0;
            repair_left(heap,alive,L,st);
        }
#ifndef NDEBUG
        if(!check_alive_strict(heap,alive)) throw std::runtime_error("pop bad");
#endif
    }
    vals.assign(desc.rbegin(), desc.rend()); return st;
}

// include weak/binary simplified from previous file? We'll just read compare with direct output later; implement weak quickly omitted? Need direct? 
static bool is_sorted_asc(const std::vector<int>& a){ return std::is_sorted(a.begin(),a.end()); }
static std::vector<int> random_vec(std::size_t n, std::mt19937& rng){ std::vector<int> v(n); std::iota(v.begin(),v.end(),1); std::shuffle(v.begin(),v.end(),rng); return v; }
static long double log2_factorial_ld(std::size_t n){ long double s=0; for(std::size_t i=2;i<=n;++i) s+=std::log2((long double)i); return s; }
int main(){ std::cout<<std::fixed<<std::setprecision(6); std::mt19937 rng(1234567); std::cout<<"padded sentinel ordered3 general n\n"; std::cout<<"n,reps,ordered,obuild,opop,alpha,o_minus_lower_per_n,sorted\n"; std::vector<std::size_t> sizes={2,3,4,5,6,7,8,9,10,15,16,17,31,32,33,63,64,65,100,127,128,129,255,256,257,511,512,513,1000,1023,1024,1025,4095,4096,4097}; for(auto n:sizes){ int reps=n<=17?2000:(n<=129?500:(n<=513?200:(n<=1025?80:20))); long double oc=0,ob=0,op=0; bool ok=true; for(int rep=0;rep<reps;++rep){ auto a=random_vec(n,rng); auto st=sort_ordered3_padded(a); if(!is_sorted_asc(a)){ok=false;break;} oc+=st.comparisons; ob+=st.build_comparisons; op+=st.pop_comparisons; } oc/=reps; ob/=reps; op/=reps; long double nlog=(long double)n*std::log2((long double)n); long double lg=log2_factorial_ld(n); std::cout<<n<<","<<reps<<","<<oc<<","<<ob<<","<<op<<","<<((nlog-oc)/(long double)n)<<","<<((oc-lg)/(long double)n)<<","<<ok<<"\n"; } }
