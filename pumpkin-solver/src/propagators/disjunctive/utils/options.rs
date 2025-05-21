


#[derive(Clone, Debug, Default, Copy)]
pub (crate) struct DisjunctivePropagatorOptions {
    pub (crate) explanation_type: DisjunctiveExplanationType
}


#[derive(Debug, Clone, Copy, Default)]
pub (crate) enum DisjunctiveExplanationType {
    #[default]
    Naive,
    PrevScheduledTasks,
    LastCluster,
}