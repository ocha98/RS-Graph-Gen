use std::collections::BTreeSet;

use rand::rngs::StdRng;
use rand::prelude::*;

/// グラフ生成器
/// 全て0-indexedで生成します
pub struct Graph {
    pub n: usize,
    pub edges: Vec<(usize, usize)>,
}

impl Graph {
    pub fn gen_tree(n: usize, rng: &mut StdRng) -> Graph {
        let mut rand_v: Vec<usize> = (0..n).collect();
        rand_v.shuffle(rng);// 頂点をランダムにするため

        let mut edges = Vec::new();
        edges.reserve(n-1);
        for i in 1..n {
            let v = rng.gen_range(0..i);
            edges.push((rand_v[v], rand_v[i]));
        }

        Graph { n, edges }
    }

    pub fn gen_simple_graph(n: usize, m: usize, connected: bool, rng: &mut StdRng) -> Graph {
        assert!(m <= n*(n-1)/2, "m must be less than or equal to n*(n-1)/2. n = {}, m = {}", n, m);
        let mut g = Graph { n, edges: Vec::new() };
        g.edges.reserve(m);
        let mut st = BTreeSet::new();
        if connected {
            assert!(m >= n-1, "m must be greater than or equal to n-1");
            let tree = Graph::gen_tree(n, rng);
            for &(u, v) in &tree.edges {
                assert!(!st.contains(&(u.min(v), u.max(v))), "Failed to generate simple graph with n = {}, m = {}", n, m);
                st.insert((u.min(v), u.max(v)));
                g.edges.push((u, v));
            }
        }
        while g.edges.len() < m {
            let u = rng.gen_range(0..n);
            let v = rng.gen_range(0..n);
            if u == v || st.contains(&(u.min(v), u.max(v))) { continue; }
            st.insert((u.min(v), u.max(v)));
            g.edges.push((u, v));
        }

        g
    }
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use super::Graph;

    #[test]
    fn test_gen_tree() {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        for n in [1, 10 ,100] {
            let g = Graph::gen_tree(n, &mut rng);
    
            assert!(g.edges.len() == n-1, "Failed to generate tree graph with n = {}", n);
            let mut to = vec![vec![]; n];
            for &(u, v) in &g.edges {
                assert!(u < n && v < n, "Failed to generate tree graph with n = {}", n);
                to[u].push(v);
                to[v].push(u);
            }
    
            let mut visited = vec![false; n];
            let mut que = VecDeque::new();
            que.push_back(0);
            while let Some(v) = que.pop_front() {
                if visited[v] { continue; }
                visited[v] = true;
                for &nxt in &to[v] {
                    if visited[nxt] { continue; }
                    que.push_back(nxt);
                }
            }
    
            assert!(visited.iter().all(|&v| v), "Failed to generate tree graph with n = {}", n);
        }
    }

    #[test]
    fn test_gen_simple_graph() {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        for n in [1, 10 ,100] {
            let m = n-1;
            let g = Graph::gen_simple_graph(n, m, true, &mut rng);
            assert_eq!(g.edges.len(), m, "Failed to generate simple graph with n = {}, m = {}", n, m);
            assert!(g.edges.len() == m, "Failed to generate simple graph with n = {}, m = {}", n, m);
            let mut st = std::collections::BTreeSet::new();
            for &(u, v) in &g.edges {
                assert!(u < n && v < n, "Failed to generate simple graph with n = {}, m = {}", n, m);
                assert_ne!(u, v, "Failed to generate simple graph with n = {}, m = {}", n, m);
                if st.contains(&(u.min(v), u.max(v))) {
                    panic!("Failed to generate simple graph with n = {}, m = {}", n, m);
                }
                st.insert((u.min(v), u.max(v)));
            }
        }
    }

    #[test]
    fn test_gen_simple_connected_graph() {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        for n in [1, 10 ,100] {
            let m = (2*n).min(n*(n-1)/2);
            let g = Graph::gen_simple_graph(n, m, true, &mut rng);
            assert_eq!(g.edges.len(), m, "Failed to generate simple graph with n = {}, m = {}", n, m);
            assert!(g.edges.len() == m, "Failed to generate simple graph with n = {}, m = {}", n, m);
            let mut st = std::collections::BTreeSet::new();
            let mut to = vec![vec![]; n];
            for &(u, v) in &g.edges {
                assert!(u < n && v < n, "Failed to generate simple graph with n = {}, m = {}", n, m);
                assert_ne!(u, v, "Failed to generate simple graph with n = {}, m = {}", n, m);
                if st.contains(&(u.min(v), u.max(v))) {
                    panic!("Failed to generate simple graph with n = {}, m = {}", n, m);
                }
                to[u].push(v);
                to[v].push(u);
                st.insert((u.min(v), u.max(v)));
            }

            let mut visited = vec![false; n];
            let mut que = VecDeque::new();
            que.push_back(0);
            while let Some(v) = que.pop_front() {
                if visited[v] { continue; }
                visited[v] = true;
                for &nxt in &to[v] {
                    if visited[nxt] { continue; }
                    que.push_back(nxt);
                }
            }

            assert!(visited.iter().all(|&v| v), "Failed to generate simple graph with n = {}, m = {}", n, m);
        }
    }
}