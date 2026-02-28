// `use crate::common::collections::seq_is_unique_v::*;
// use crate::common::collections::vecs::*;
// use crate::implementation::common::{generic_refinement::*, upper_bound::*};
// use crate::implementation::RSL::{cconfiguration::*, cconstants::*, cmessage::*, types_i::*};
// use crate::protocol::common::upper_bound::*;
// use crate::protocol::RSL::{
//     configuration::*, constants::*, election::*, environment::*, message::*, types::*,
// };
// use builtin::*;
// use builtin_macros::*;
// use std::collections::*;
// use vstd::{map::*, prelude::*, seq::*, set::*};

// verus! {

// #[derive(Clone)]
// pub struct CElectionState {
//     pub constants: CReplicaConstants,
//     pub current_view: CBallot,
//     pub current_view_suspectors: HashSet<u64>,
//     pub epoch_end_time: u64,
//     pub epoch_length: u64,
//     pub requests_received_this_epoch: Vec<CRequest>,
//     pub requests_received_prev_epochs: Vec<CRequest>,
// }

// impl CElectionState {
//     pub open spec fn abstractable(self) -> bool {
//         &&& self.constants.abstractable()
//         &&& self.current_view.abstractable()
//         &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].abstractable())
//         &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].abstractable())
//     }

//     pub open spec fn valid(self) -> bool {
//         &&& self.abstractable()
//         &&& self.constants.valid()
//         &&& self.current_view.valid()
//         &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].valid())
//         &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].valid())
//     }

//     pub open spec fn view(self) -> ElectionState
//         recommends self.abstractable()
//     {
//         ElectionState{
//             constants: self.constants@,
//             current_view: self.current_view@,
//             current_view_suspectors: self.current_view_suspectors@.map(|x:u64| x as int),
//             epoch_end_time: self.epoch_end_time as int,
//             epoch_length: self.epoch_length as int,
//             requests_received_this_epoch: self.requests_received_this_epoch@.map(|i, r:CRequest| r@),
//             requests_received_prev_epochs: self.requests_received_prev_epochs@.map(|i, r:CRequest| r@)
//         }
//     }

//     pub fn CComputeSuccessorView(b:CBallot, c:CConstants) -> (rc:CBallot)
//         requires
//             b.valid(),
//             c.valid(),
//             b.seqno < 0xFFFF_FFFF_FFFF_FFFF
//         ensures
//             rc.valid(),
//             rc@ == ComputeSuccessorView(b@, c@),
//     {
//         if b.proposer_id + 1 < c.config.replica_ids.len() as u64 {
//             CBallot{seqno:b.seqno, proposer_id:b.proposer_id+1}
//         } else {
//             CBallot{seqno:b.seqno+1, proposer_id:0}
//         }
//     }

//     pub fn CBoundRequestSequence(s: Vec<CRequest>, lengthBound: u64) -> (rc: Vec<CRequest>)
//         requires
//             s@.len() < 0x1_0000_0000_0000_0000,
//             forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
//         ensures
//             forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
//             rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}),
//     {
//         let s_len = s.len() as u64;
//         assert(s_len == s@.len() as u64);
//         if 0 <= lengthBound && lengthBound < s_len {
//             let rc = truncate_vec(&s, 0, lengthBound as usize);
//             assert(rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}));
//             rc
//         } else {
//             let rc = s;
//             assert(rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}));
//             rc
//         }
//     }

//     pub fn CRequestsMatch(r1:CRequest, r2:CRequest) -> (r:bool)
//         requires
//             r1.valid(),
//             r2.valid(),
//         ensures
//             r == RequestsMatch(r1@, r2@)
//     {
//         do_end_points_match(&r1.client, &r2.client) && r1.seqno == r2.seqno
//     }

//     pub fn CRequestSatisfiedBy(r1:CRequest, r2:CRequest) -> (r:bool)
//         requires
//             r1.valid(),
//             r2.valid(),
//         ensures
//             r == RequestSatisfiedBy(r1@, r2@),
//     {
//         do_end_points_match(&r1.client, &r2.client) && r1.seqno <= r2.seqno
//     }

//     #[verifier(external_body)]
//     pub fn CRemoveAllSatisfiedRequestsInSequence(s:&Vec<CRequest>, r:&CRequest) -> (rc: Vec<CRequest>)
//         where CRequest: Clone
//         requires
//             forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
//             r.valid(),
//         ensures
//             forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
//             rc@.map(|i, req:CRequest| req@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@),
//     {
//         let mut rc = Vec::new();
//         for i in 0 ..s.len(){
//             if !Self::CRequestSatisfiedBy(s[i].clone(), r.clone()){
//                 rc.push(s[i].clone());
//             }
//         }
//         rc
//     }

//     // #[verifier(external_body)]
//     pub fn CElectionStateInit(c:CReplicaConstants) -> (rc:Self)
//         requires
//             c.valid(),
//             c.all.config.replica_ids.len() > 0,
//         ensures
//             rc.valid(),
//             ElectionStateInit(rc@, c@),
//     {
//         let election = CElectionState{
//             constants: c,
//             current_view: CBallot{seqno:1, proposer_id:0},
//             current_view_suspectors: HashSet::new(),
//             epoch_end_time: 0,
//             epoch_length: c.all.params.baseline_view_timeout_period,
//             requests_received_this_epoch: Vec::new(),
//             requests_received_prev_epochs: Vec::new(),
//         };
//         assert(election@.constants == c@);
//         assert(election@.current_view == Ballot{seqno:1, proposer_id:0});
//         assert(election@.current_view_suspectors == Set::empty());
//         assert(election@.epoch_end_time == 0);
//         assert(election@.epoch_length == c.all.params.baseline_view_timeout_period);
//         assert(election@.requests_received_this_epoch == Seq::empty());
//         assert(election@.requests_received_prev_epochs == Seq::empty());

//         election

//     }

//     // #[verifier(external_body)]
//     pub fn CElectionStateProcessHeartbeat(
//         &mut self,
//         p:CPacket,
//         clock:u64
//     )
//         requires
//             old(self).valid(),
//             p.msg is CMessageHeartbeat,
//             p.valid(),
//         ensures
//             self.valid(),
//             ElectionStateProcessHeartbeat(old(self)@, self@, p@, clock as int)
//     {
//         //start from here
//         let CMessage::CMessageHeartbeat{bal_heartbeat, suspicious, .. } = p.msg else { unreachable!() };
//         let src_ep = p.src;
//         let mut index = 0;
//         let mut found = false;
//         for i in 0..self.constants.all.config.replica_ids.len() {
//             if self.constants.all.config.replica_ids[i] == src_ep {
//                 found = true;
//                 index = i as u64;
//                 break;
//             }
//         }
//         if !found {
//             return;
//         }
//         if bal_heartbeat == self.current_view && suspicious {
//             self.current_view_suspectors.insert(index);
//         } else if CBalLt(&self.current_view, bal_heartbeat) {
//             let new_epoch_length = UpperBoundedAdditionImpl(
//                 self.epoch_length,
//                 self.epoch_length,
//                 self.constants.all.params.max_integer_val,
//             );
//             let new_epoch_end_time = UpperBoundedAdditionImpl(
//                 clock,
//                 new_epoch_length,
//                 self.constants.all.params.max_integer_val,
//             );

//            let mut new_seq = self.requests_received_prev_epochs.clone();
//            new_seq.extend(self.requests_received_this_epoch.clone());
//            self.requests_received_prev_epochs = Self::CBoundRequestSequence(
//             new_seq,
//             self.constants.all.params.max_integer_val,
//            );
//            self.requests_received_this_epoch = Vec::new();

//            self.current_view = bal_heartbeat;
//            self.current_view_suspectors = if suspicious { HashSet::from_iter([index]) } else { HashSet::new() };
//            self.epoch_length = new_epoch_length;
//            self.epoch_end_time = new_epoch_end_time;

//         }
//     }
//          //start here

//     // #[verifier(external_body)]
//     pub fn CElectionStateCheckForViewTimeout(
//         &mut self,
//         clock:u64
//     )
//         requires
//             old(self).valid(),
//         ensures
//             self.valid(),
//             ElectionStateCheckForViewTimeout(old(self)@, self@, clock as int)
//     {
//         if clock < self.epoch_end_time {
//             return;
//         }
//         if self.requests_received_prev_epochs.is_empty() {
//             let new_epoch_length = self.constants.all.params.baseline_view_timeout_period;
//             let new_epoch_end_time = UpperBoundedAdditionImpl(
//                 clock,
//                 new_epoch_length,
//                 self.constants.all.params.max_integer_val,
//             );
//             self.requests_received_prev_epochs = self.requests_received_this_epoch.clone();
//             self.requests_received_this_epoch = Vec::new();
//             self.epoch_length = new_epoch_length;
//             self.epoch_end_time = new_epoch_end_time;

//         } else {
//             self.current_view_suspectors.insert(self.constants.my_index as u64);
//             let new_epoch_length = UpperBoundedAdditionImpl(
//               clock,
//               self.epoch_length,
//               self.constants.all.params.max_integer_val,
//             );
//             let mut new_seq = self.requests_received_prev_epochs.clone();
//             new_seq.extend(self.requests_received_this_epoch.clone());
//             self.requests_received_prev_epochs = Self::CBoundRequestSequence(
//                 new_seq,
//                 self.constants.all.params.max_integer_val,
//             );
//             self.requests_received_this_epoch = Vec::new();
//             self.epoch_length = new_epoch_length;

//         }
//     }

//     // #[verifier(external_body)]
//     pub fn CElectionStateCheckForQuorumOfViewSuspicions(
//         &mut self,
//         clock:u64
//     )
//         requires
//             old(self).valid(),
//         ensures
//             self.valid(),
//             ElectionStateCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int)
//     {
//         let min_quorum_size = self.constants.all.config.CMinQuorumSize();
//         if self.current_view_suspectors.len() < min_quorum_size as usize || self.current_view_seqno >= self.constants.all.params.max_integer_val {
//             return;
//         }
//         let new_view = Self::CComputeSuccessorView(self.current_view,self.constants.all);
//         let new_epoch_length = UpperBoundedAdditionImpl(
//             self.epoch_length,
//             self.epoch_length,
//             self.constants.all.params.max_integer_val,
//         );
//         let new_epoch_end_time = UpperBoundedAdditionImpl(
//             clock,
//             new_epoch_length,
//             self.constants.all.params.max_integer_val,
//         );

//         let mut new_seq = self.requests_received_prev_epochs.clone();
//         new_seq.extend(self.requests_received_this_epoch.clone());
//         self.requests_received_prev_epochs = Self::CBoundRequestSequence(
//             new_seq,
//             self.constants.all.params.max_integer_val,
//         );
//         self.requests_received_this_epoch = Vec::new();

//         self.current_view = new_view;
//         self.current_view_suspectors = HashSet::new();
//         self.epoch_length = new_epoch_length;
//         self.epoch_end_time = new_epoch_end_time;
//     }

//     // #[verifier(external_body)]
//     pub fn CElectionStateReflectReceivedRequest(
//         &mut self,
//         req:CRequest
//     )
//         requires
//             old(self).valid(),
//             req.valid(),
//         ensures
//             self.valid(),
//             ElectionStateReflectReceivedRequest(old(self)@, self@, req@)
//     {
//         let header = CRequestHeader { client: req.client, seqno: req.seqno };
//         let mut earlier = false;
//         for r in &self.requests_received_this_epoch {
//             if Self::CRequestsMatch(r.clone(),req.clone()) {
//                 earlier = true;
//                 break;
//             }

//         }
//         if !earlier {
//             for r in &self.requests_received_prev_epochs {
//                 if Self::CRequestsMatch(r.clone(),req.clone()) {
//                     earlier = true;
//                     break;
//                 }
//             }
//         }
//         if !earlier {
//            let mut new_seq = self.requests_received_this_epoch.clone();
//            new_seq.push(req);
//            self.requests_received_this_epoch = Self::CBoundRequestSequesce(
//             new_seq,
//             self.constants.all.params.max_integer_val,
//            );
//         }

//     }

//     // #[verifier(external_body)]
//     pub fn CRemoveExecutedRequestBatch(reqs: Vec<CRequest>, batch: CRequestBatch) -> (r: Vec<CRequest>)
//         requires
//             (forall |i: int| 0 <= i < reqs@.len() ==> reqs@[i].valid()),
//             crequestbatch_is_valid(batch),
//         ensures
//             (forall |i: int| 0 <= i < r@.len() ==> r@[i].valid()),
//             r@.map(|i, req:CRequest| req@) == RemoveExecutedRequestBatch(reqs@.map(|i, req:CRequest| req@), abstractify_crequestbatch(batch)),
//     {
//         let mut result = reqs.clone();
//         for i in 0..batch.len() {
//             result = Self::CRemoveAllSatisfiedRequestsInSequence(&result,&batch[i]);
//         }
//         result

//     }

//     // #[verifier(external_body)]
//     pub fn ElectionStateReflectExecutedRequestBatch(
//         &mut self,
//         batch:CRequestBatch
//     )
//         requires
//             old(self).valid(),
//             crequestbatch_is_valid(batch),
//         ensures
//             self.valid(),
//             ElectionStateReflectExecutedRequestBatch(old(self)@, self@, abstractify_crequestbatch(batch))
//     {
//         self.requests_received_prev_epochs = Self::CRemoveExecutedRequestBatch(
//             self.requests_received_prev_epochs.clone(),
//             batch.clone(),
//         );
//         self.requests_received_this_epoch = Self::CRemoveExecutedRequestBatch(
//             self.requests_received_this_epoch.clone(),
//             batch,

//         );

//     }
// }

// } // verus!

use crate::common::collections::seq_is_unique_v::*;
use crate::common::collections::vecs::*;
use crate::implementation::common::{generic_refinement::*, upper_bound::*};
use crate::implementation::RSL::{cconfiguration::*, cconstants::*, cmessage::*, types_i::*};
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::{
    configuration::*, constants::*, election::*, environment::*, message::*, types::*,
};
use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::{map::*, prelude::*, seq::*, set::*};

verus! {

#[derive(Clone)]
pub struct CElectionState {
    pub constants: CReplicaConstants,
    pub current_view: CBallot,
    pub current_view_suspectors: HashSet<u64>,
    pub epoch_end_time: u64,
    pub epoch_length: u64,
    pub requests_received_this_epoch: Vec<CRequest>,
    pub requests_received_prev_epochs: Vec<CRequest>,
}

impl CElectionState{
    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& self.current_view.abstractable()
        &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].abstractable())
        &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].abstractable())
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& self.current_view.valid()
        &&& (forall |i:int| 0 <= i < self.requests_received_this_epoch@.len() ==> self.requests_received_this_epoch@[i].valid())
        &&& (forall |i:int| 0 <= i < self.requests_received_prev_epochs@.len() ==> self.requests_received_prev_epochs@[i].valid())
    }

    pub open spec fn view(self) -> ElectionState
        recommends self.abstractable()
    {
        ElectionState{
            constants: self.constants@,
            current_view: self.current_view@,
            current_view_suspectors: self.current_view_suspectors@.map(|x:u64| x as int),
            epoch_end_time: self.epoch_end_time as int,
            epoch_length: self.epoch_length as int,
            requests_received_this_epoch: self.requests_received_this_epoch@.map(|i, r:CRequest| r@),
            requests_received_prev_epochs: self.requests_received_prev_epochs@.map(|i, r:CRequest| r@)
        }
    }

    pub fn CComputeSuccessorView(b:CBallot, c:CConstants) -> (rc:CBallot)
        requires
            b.valid(),
            c.valid(),
            b.seqno < 0xFFFF_FFFF_FFFF_FFFF
        ensures
            rc.valid(),
            rc@ == ComputeSuccessorView(b@, c@),
    {
        if b.proposer_id + 1 < c.config.replica_ids.len() as u64 {
            CBallot{seqno:b.seqno, proposer_id:b.proposer_id+1}
        } else {
            CBallot{seqno:b.seqno+1, proposer_id:0}
        }
    }

    pub fn CBoundRequestSequence(s: Vec<CRequest>, lengthBound: u64) -> (rc: Vec<CRequest>)
        requires
            s@.len() < 0x1_0000_0000_0000_0000,
            forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
        ensures
            forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
            rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}),
    {
        let s_len = s.len() as u64;
        assert(s_len == s@.len() as u64);
        if 0 <= lengthBound && lengthBound < s_len {
            let rc = truncate_vec(&s, 0, lengthBound as usize);
            assert(rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}));
            rc
        } else {
            let rc = s;
            assert(rc@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(|i, r: CRequest| r@), UpperBound::UpperBoundFinite{n: lengthBound as int}));
            rc
        }
    }

    pub fn CRequestsMatch(r1:CRequest, r2:CRequest) -> (r:bool)
        requires
            r1.valid(),
            r2.valid(),
        ensures
            r == RequestsMatch(r1@, r2@)
    {
        do_end_points_match(&r1.client, &r2.client) && r1.seqno == r2.seqno
    }

    pub fn CRequestSatisfiedBy(r1:CRequest, r2:CRequest) -> (r:bool)
        requires
            r1.valid(),
            r2.valid(),
        ensures
            r == RequestSatisfiedBy(r1@, r2@)
    {
        do_end_points_match(&r1.client, &r2.client) && r1.seqno <= r2.seqno
    }

    #[verifier(external_body)]
    pub fn CRemoveAllSatisfiedRequestsInSequence(s:&Vec<CRequest>, r:&CRequest) -> (rc: Vec<CRequest>)
        where CRequest: Clone
        requires
            forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
            r.valid(),
        ensures
            forall |i: int| 0 <= i < rc@.len() ==> rc@[i].valid(),
            rc@.map(|i, req:CRequest| req@) == RemoveAllSatisfiedRequestsInSequence(s@.map(|i, req: CRequest| req@), r@),
    {
        let mut rc: Vec<CRequest> = Vec::new();
        for req in s {
            if !Self::CRequestSatisfiedBy(req.clone_up_to_view(), r.clone_up_to_view()) {
                rc.push(req.clone_up_to_view());
            }
        }
        rc
    }

    // #[verifier(external_body)]
    pub fn CElectionStateInit(c:CReplicaConstants) -> (rc:Self)
        requires
            c.valid(),
            c.all.config.replica_ids.len() > 0
        ensures
            rc.valid(),
            ElectionStateInit(rc@, c@),
    {


        //CHECK AGAIN
        CElectionState {
            constants: c.clone(),
            current_view: CBallot{seqno:1, proposer_id:0},
            current_view_suspectors: HashSet::new(),
            epoch_end_time: 0,
            epoch_length: c.all.params.baseline_view_timeout_period,
            requests_received_this_epoch: Vec::new(),
            requests_received_prev_epochs: Vec::new()
        }
    }

    // #[verifier(external_body)]
    pub fn CElectionStateProcessHeartbeat(
        &mut self,
        p:CPacket,
        clock:u64
    )
        requires
            old(self).valid(),
            p.msg is CMessageHeartbeat,
            p.valid(),
        ensures
            self.valid(),
            ElectionStateProcessHeartbeat(old(self)@, self@, p@, clock as int)
    {
        let sender = p.src;
        let (found, idx) = self.constants.all.config.CGetReplicaIndex(sender);
        if !found {
            // unknown sender ⇒ no change
            return;
        }
        let CMessage::CMessageHeartbeat{bal_heartbeat, suspicious, .. } = p.msg else { unreachable!() };

        if self.current_view == bal_heartbeat && suspicious {
            // Same view, suspicious: just insert sender into suspectors
            self.current_view_suspectors.insert(idx as u64);
        } else if CBalLt(&self.current_view, &bal_heartbeat) {
            // Newer view: update view, reset suspectors appropriately, and roll epoch
            let doubled = CUpperBoundedAddition(
                self.epoch_length,
                self.epoch_length,
                self.constants.all.params.max_integer_val,
            );
            let new_end = CUpperBoundedAddition(clock, doubled, self.constants.all.params.max_integer_val);

            let mut merged = self.requests_received_prev_epochs.clone();
            merged.extend(self.requests_received_this_epoch.clone());
            let bounded = CElectionState::CBoundRequestSequence(merged, self.constants.all.params.max_integer_val);

            self.current_view = bal_heartbeat.clone_up_to_view();
            self.current_view_suspectors = if suspicious {
                let mut s = std::collections::HashSet::new();
                s.insert(idx as u64);
                s
            } else {
                std::collections::HashSet::new()
            };
            self.epoch_length = doubled;
            self.epoch_end_time = new_end;
            self.requests_received_prev_epochs = bounded;
            self.requests_received_this_epoch.clear();
        } // else: unchanged

    }
    // #[verifier(external_body)]
    pub fn CElectionStateCheckForViewTimeout(
        &mut self,
        clock:u64
    )
        requires
            old(self).valid(),
        ensures
            self.valid(),
            ElectionStateCheckForViewTimeout(old(self)@, self@, clock as int)
    {
        if clock < self.epoch_end_time {
            return;
        }
        if self.requests_received_prev_epochs.is_empty() {
            let new_epoch_length = self.constants.all.params.baseline_view_timeout_period;
            let new_epoch_end_time = CUpperBoundedAddition(
                clock,
                new_epoch_length,
                self.constants.all.params.max_integer_val,
            );
            self.requests_received_prev_epochs = self.requests_received_this_epoch.clone();
            self.requests_received_this_epoch.clear();
            self.epoch_length = new_epoch_length;
            self.epoch_end_time = new_epoch_end_time;
        } else {
            self.current_view_suspectors.insert(self.constants.my_index as u64);
            let new_end = CUpperBoundedAddition(
                clock,
                self.epoch_length,
                self.constants.all.params.max_integer_val,
            );
            let mut merged = self.requests_received_prev_epochs.clone();
            merged.extend(self.requests_received_this_epoch.clone());
            let bounded = CElectionState::CBoundRequestSequence(merged, self.constants.all.params.max_integer_val);
            self.requests_received_prev_epochs = bounded;
            self.requests_received_this_epoch.clear();
            self.epoch_end_time = new_end;
        }
    }

    // #[verifier(external_body)]
    pub fn CElectionStateCheckForQuorumOfViewSuspicions(
        &mut self,
        clock:u64
    )
        requires
            old(self).valid(),
        ensures
            self.valid(),
            ElectionStateCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int)
    {
        let minq = self.constants.all.config.CMinQuorumSize();
        if self.current_view_suspectors.len() < minq as usize || self.current_view.seqno >= self.constants.all.params.max_integer_val {
            return;
        }
        let new_view = CElectionState::CComputeSuccessorView(self.current_view.clone_up_to_view(), self.constants.all.clone());
        self.current_view = new_view;
        self.current_view_suspectors.clear();
        let doubled = CUpperBoundedAddition(
            self.epoch_length,
            self.epoch_length,
            self.constants.all.params.max_integer_val,
        );
        self.epoch_length = doubled;
        self.epoch_end_time = CUpperBoundedAddition(
            clock,
            doubled,
            self.constants.all.params.max_integer_val,
        );

        let mut merged = self.requests_received_prev_epochs.clone();
        merged.extend(self.requests_received_this_epoch.clone());


        let bounded = CElectionState::CBoundRequestSequence(merged, self.constants.all.params.max_integer_val);
        self.requests_received_prev_epochs = bounded;
        self.requests_received_this_epoch.clear();
    }


    // #[verifier(external_body)]
    pub fn CElectionStateReflectReceivedRequest(
        &mut self,
        req:CRequest
    )
        requires
            old(self).valid(),
            req.valid(),
        ensures
            self.valid(),
            ElectionStateReflectReceivedRequest(old(self)@, self@, req@)
    {
        let mut earlier = false;
        for r in &self.requests_received_this_epoch {
            if Self::CRequestsMatch(r.clone_up_to_view(), req.clone_up_to_view()) {
                earlier = true;
                break;
            }
        }
        if !earlier {
            for r in &self.requests_received_prev_epochs {
                if Self::CRequestsMatch(r.clone_up_to_view(), req.clone_up_to_view()) {
                    earlier = true;
                    break;
                }
            }
        }

        if !earlier {
            let mut new_seq = self.requests_received_this_epoch.clone();
            new_seq.push(req.clone_up_to_view());
            self.requests_received_this_epoch = CElectionState::CBoundRequestSequence(
                new_seq,
                self.constants.all.params.max_integer_val,
            );
        }
    }

    // #[verifier(external_body)]
    pub fn CRemoveExecutedRequestBatch(reqs: Vec<CRequest>, batch: CRequestBatch) -> (r: Vec<CRequest>)
        requires
            (forall |i: int| 0 <= i < reqs@.len() ==> reqs@[i].valid()),
            crequestbatch_is_valid(batch),
        ensures
            (forall |i: int| 0 <= i < r@.len() ==> r@[i].valid()),
            r@.map(|i, req:CRequest| req@) == RemoveExecutedRequestBatch(reqs@.map(|i, req:CRequest| req@), abstractify_crequestbatch(batch)),
    {
       let mut reqs = reqs;
       for creq in batch.iter() {
           reqs = Self::CRemoveAllSatisfiedRequestsInSequence(&reqs, creq);
       }
       reqs
    }

    // #[verifier(external_body)]
    pub fn ElectionStateReflectExecutedRequestBatch(
        &mut self,
        batch:CRequestBatch
    )
        requires
            old(self).valid(),
            crequestbatch_is_valid(batch),
        ensures
            self.valid(),
            ElectionStateReflectExecutedRequestBatch(old(self)@, self@, abstractify_crequestbatch(batch))
    {
        self.requests_received_prev_epochs = Self::CRemoveExecutedRequestBatch(
            self.requests_received_prev_epochs.clone(),
            batch.clone(),
        );
        self.requests_received_this_epoch = Self::CRemoveExecutedRequestBatch(
            self.requests_received_this_epoch.clone(),
            batch,
        );
    }
}

} // verus!
