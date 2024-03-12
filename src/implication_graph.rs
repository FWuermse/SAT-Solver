use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ImplicationGraphNode {
    pub(crate) literal: i32,
    pub(crate) decision_level: u32,
    pub(crate) reason: Option<usize>,
    pub(crate) predecessors: Vec<i32>,
}

#[derive(Debug, Clone)]
pub(crate) struct ImplicationGraph(pub HashMap<i32, ImplicationGraphNode>);

impl ImplicationGraph {
    pub(crate) fn new() -> Self {
        ImplicationGraph(HashMap::new())
    }
    pub(crate) fn insert_leaf(&mut self, var: i32, depth: u32) {
        self.0.entry(var.abs()).or_insert(ImplicationGraphNode {
            literal: var,
            decision_level: depth,
            reason: None,
            predecessors: vec![],
        });
    }
    pub(crate) fn insert_conflict_node(&mut self, c_idx: usize, vars: Vec<i32>, depth: u32) {
        self.0.insert(
            0,
            ImplicationGraphNode {
                literal: 0,
                decision_level: depth,
                reason: Some(c_idx),
                predecessors: vars.iter().map(|v| v.abs()).collect(),
            },
        );
    }
    pub(crate) fn insert_edge(&mut self, vars: Vec<i32>, source: i32, c_idx: usize, depth: u32) {
        let vars = vars
            .iter()
            .filter(|&v| self.0.get(&v.abs()).is_some())
            .map(|v| *v)
            .collect::<Vec<i32>>();
        if self.0.contains_key(&source.abs()) {
            print!("test");
        }
        self.0.entry(source.abs()).or_insert(ImplicationGraphNode {
            literal: source,
            decision_level: depth,
            reason: Some(c_idx),
            predecessors: vars.iter().map(|v| v.abs()).collect(),
        });
    }
    pub(crate) fn get_conflict_node(&self) -> Result<&ImplicationGraphNode, String> {
        match self.0.get(&0) {
            Some(v) => Ok(v),
            None => Err("No conflict node was found at this moment.".into()),
        }
    }

    pub(crate) fn clear_conflict(&mut self) {
        self.0.remove(&0);
    }
    pub(crate) fn update_implication_graph(&mut self, valid_level: u32) {
        self.0.retain(|_, node| node.decision_level <= valid_level);
    }
}
