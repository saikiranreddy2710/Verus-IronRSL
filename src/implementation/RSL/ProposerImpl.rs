// use crate::common::collections::vecs::concat_vecs;
// use crate::common::native::io_s::*;
// use crate::implementation::common::generic_refinement::*;
// use crate::implementation::common::upper_bound::*;
// use crate::implementation::RSL::cbroadcast::*;
// use crate::implementation::RSL::cconfiguration::*;
// use crate::implementation::RSL::cconstants::*;
// use crate::implementation::RSL::cmessage::*;
// use crate::implementation::RSL::types_i::*;
// use crate::implementation::RSL::ElectionImpl::*;
// use crate::protocol::RSL::proposer::*;
// use builtin::*;
// use builtin_macros::*;
// use std::collections::*;
// use vstd::invariant;
// use vstd::{map::*, prelude::*, seq::*, set::*};

// verus! {

// #[derive(Clone)]
// pub enum CIncompleteBatchTimer{
//     CIncompleteBatchTimerOn {when:u64},
//     CIncompleteBatchTimerOff,
// }

// impl CIncompleteBatchTimer{

//     pub open spec fn abstractable(self) -> bool {
//         match self {
//             CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => true,
//             CIncompleteBatchTimer::CIncompleteBatchTimerOff => true,
//         }
//     }

//     pub open spec fn valid(self) -> bool {
//         match self {
//             CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => self.abstractable(),
//             CIncompleteBatchTimer::CIncompleteBatchTimerOff => self.abstractable(),
//         }
//     }

//     pub open spec fn view(self) -> IncompleteBatchTimer
//         recommends
//         self.abstractable(),
//     {
//         match self {
//             CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => IncompleteBatchTimer::IncompleteBatchTimerOn {when:when as int},
//             CIncompleteBatchTimer::CIncompleteBatchTimerOff => IncompleteBatchTimer::IncompleteBatchTimerOff{},
//         }
//     }

// }

// #[derive(Clone)]
// pub struct CElectionState {
//     pub constants: CReplicaConstants,
//     pub current_view: CBallot,
//     pub current_view_suspectors: HashSet<u64>,
//     pub epoch_end_time: u64,
//     pub epoch_length: u64,
//     pub requests_received_this_epoch: Vec<CRequest>,
//     pub requests_received_prev_epochs: Vec<CRequest>,
//     pub cur_req_set: HashSet<CRequestHeader>,
//     pub prev_req_set: HashSet<CRequestHeader>,
// }

// pub struct CProposer {
//     pub constants: CReplicaConstants,
//     pub current_state: u64,
//     pub request_queue: Vec<CRequest>,
//     pub max_ballot_i_sent_1a: CBallot,
//     pub next_operation_number_to_propose: u64,
//     pub received_1b_packets: HashSet<CPacket>,
//     pub highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>,
//     pub incomplete_batch_timer: CIncompleteBatchTimer,
//     pub election_state: CElectionState,
//     pub max_opn_with_proposal: COperationNumber,
//     pub max_log_truncation_point: COperationNumber,
// }

// impl CProposer{

//     pub open spec fn abstractable(self) -> bool {
//         &&& self.constants.abstractable()
//         &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable())
//         &&& self.max_ballot_i_sent_1a.abstractable()
//         &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable())
//         &&& (forall |k:EndPoint, v:u64| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable())
//         &&& self.incomplete_batch_timer.abstractable()
//         &&& self.election_state.abstractable()
//         &&& COperationNumberIsAbstractable(self.max_opn_with_proposal)
//         &&& COperationNumberIsAbstractable(self.max_log_truncation_point)
//     }

//     pub open spec fn valid(self) -> bool {
//         &&& self.abstractable()
//         &&& self.constants.valid()
//         &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].valid())
//         &&& self.max_ballot_i_sent_1a.valid()
//         &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.valid())
//         &&& (forall |k:EndPoint, v:u64| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.valid_public_key())
//         &&& self.incomplete_batch_timer.valid()
//         &&& self.election_state.valid()
//     }

//     pub open spec fn view(self) -> LProposer
//     recommends self.valid(),
//     {
//         LProposer{
//             constants: self.constants.view(),
//             current_state: self.current_state as int,
//             request_queue: self.request_queue@.map(|i, r:CRequest| r.view()),
//             max_ballot_i_sent_1a: self.max_ballot_i_sent_1a.view(),
//             next_operation_number_to_propose: self.next_operation_number_to_propose as int,
//             received_1b_packets: self.received_1b_packets@.map(|p:CPacket| p.view()),
//             highest_seqno_requested_by_client_this_view: Map::new(
//                 |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
//                 |ak: AbstractEndPoint| {
//                     let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
//                     self.highest_seqno_requested_by_client_this_view@[k] as int
//                 }
//             ),
//             incomplete_batch_timer: self.incomplete_batch_timer.view(),
//             election_state: self.election_state.view(),
//         }
//     }

//     // #[verifier(external_body)]
//     pub fn CIsAfterLogTruncationPoint(opn:COperationNumber, received_1b_packets:HashSet<CPacket>) -> bool
//     {
//         for p in received_1b_packets.iter() {
//             if let CMessage::CMessage1b { log_truncation_point,.. } = &p.msg {
//                 if log_truncation_point.n > opn.n {
//                     return false;
//                 }
//             }
//         }
//         true

//     }

//     // #[verifier(external_body)]
//     pub fn CSetOfMessage1b(S : HashSet<CPacket>) -> bool
//     {
//        for p in S.iter(){
//         if let CMessage::CMessage1b { .. } = p.msg {
//             // ok
//         } else {
//             return false;
//         }
//        }

//        true
//     }

//     // #[verifier(external_body)]
//     pub fn CSetOfMessage1bAboutBallot(S:HashSet<CPacket>, b:CBallot) -> bool
//     {
//         if !Self::CSetOfMessage1b(S) {
//             return false;
//         }
//     for p in S.iter() {
//         if let CMessage::CMessage1b { bal_1b, .. } = &p.msg {
//             if *bal_1b != b {
//                 return false;
//             }
//         }
//     }

//         true
//     }

//     // #[verifier(external_body)]
//     pub fn CAllAcceptorsHadNoProposal(S:HashSet<CPacket>, opn:COperationNumber) -> (result_CAllAcceptorsHadNoProposal:bool)
//     requires
//         forall |p:CPacket| S@.contains(p) ==> p.valid(),
//         COperationNumberIsValid(opn),
//         ({
//             forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
//         })
//     ensures
//         ({
//             let lr = LAllAcceptorsHadNoProposal(S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
//             result_CAllAcceptorsHadNoProposal == lr
//         })
//     {
//         for p in S.iter() {
//             let CMessage::CMessage1b { votes, ..} = &p.msg else { unreachable!()};
//             if votes.v.contains_key(opn) {
//                 return false;
//             }

//         }
//         true

//     }

//     // #[verifier(external_body)]
//     pub fn CExistVotesHasProposalLargeThanOpn(p: CPacket, op: COperationNumber) -> (result_CExistVotesHasProposalLargeThanOpn:bool)
//     requires
//         p.valid(),
//         COperationNumberIsValid(op),
//         p.msg is CMessage1b
//     ensures
//     ({
//         let lr = LExistVotesHasProposalLargeThanOpn(p.view(), AbstractifyCOperationNumberToOperationNumber(op));
//         result_CExistVotesHasProposalLargeThanOpn == lr
//     })
//     {
//         let CMessage::CMessage1b { votes, ..} = &p.msg else { unreachable!()};
//         for (opn, _) in votes.v.iter() {
//             if opn.n > op.n {
//                 return true;
//             }
//         }
//         false
//     }

//     // #[verifier(external_body)]
//     pub fn CExistsAcceptorHasProposalLargeThanOpn(S:HashSet<CPacket>, op:COperationNumber) -> (result_CExistsAcceptorHasProposalLargeThanOpn:bool)
//     requires
//         forall |p:CPacket| S@.contains(p) ==> p.valid(),
//         COperationNumberIsValid(op),
//         ({
//             forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
//         })
//     ensures
//     ({
//         let lr = LExistsAcceptorHasProposalLargeThanOpn(S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(op));
//         result_CExistsAcceptorHasProposalLargeThanOpn == lr
//     })

//     {
//         for p in S.iter() {
//             if Self::CExistVotesHasProposalLargeThanOpn(p.clone(),op) {
//                 return true;
//             }
//         }

//         false
//     }

//     // #[verifier(external_body)]
//     pub fn Cmax_balInS(c:CBallot, S:HashSet<CPacket>, opn:COperationNumber) -> (result_Cmax_balInS:bool)
//     requires
//         c.valid(),
//         forall |p:CPacket| S@.contains(p) ==> p.valid(),
//         COperationNumberIsValid(opn),
//         ({
//             forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
//         })
//     ensures
//     ({
//         let lr = Lmax_balInS(c.view(),S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
//         result_Cmax_balInS == lr
//     })
//     {
//         for p in S.iter() {
//             let CMessage::CMessage1b { votes, ..} = &p.msg else { unreachable!()};
//             if let Some(vote) = votes.v.get(&opn) {
//                 if !CBalLt(vote.max_value_bal, c) {
//                     return false;
//                 }
//             }
//         }
//         true

//     }

//     // #[verifier(external_body)]
//     pub fn CExistsBallotInS(v: CRequestBatch, c: CBallot, S: HashSet<CPacket>, opn:COperationNumber) -> (result_CExistsBallotInS:bool)
//     requires
//         crequestbatch_is_valid(v),
//         c.valid(),
//         forall |p:CPacket| S@.contains(p) ==> p.valid(),
//         COperationNumberIsValid(opn),
//         ({
//             forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
//         })
//     ensures
//     ({
//         let lr = LExistsBallotInS(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
//         result_CExistsBallotInS == lr
//     })
//     {
//         for p in S.iter() {
//             if let CMessage::CMessag1b { votes, .. } = &p.msg {
//                 if let Some(vote) = votes.v.get(&opn) {
//                     if vote.max_value_bal == c {
//                         return true;
//                     }
//                 }
//             }
//         }
//         false

//     }

//     // #[verifier(external_body)]
//     pub fn CValIsHighestNumberedProposalAtBallot(v:CRequestBatch, c:CBallot, S:HashSet<CPacket>, opn:COperationNumber) -> (result_CValIsHighestNumberedProposalAtBallot:bool)
//     requires
//         crequestbatch_is_valid(v),
//         c.valid(),
//         forall |p:CPacket| S@.contains(p) ==> p.valid(),
//         COperationNumberIsValid(opn),
//         ({
//             forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
//         })
//     ensures
//     ({
//         let lr = LValIsHighestNumberedProposalAtBallot(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
//         result_CValIsHighestNumberedProposalAtBallot == lr
//     })
//     {
//         Self::Cmax_balInS(c, S, opn) && Self::CExistsBallotInS(v, c, S, opn)
//     }

//     // #[verifier(external_body)]
//     pub fn CValIsHighestNumberedProposal(v: CRequestBatch, S: HashSet<CPacket>, opn:COperationNumber ) -> (result_CValIsHighestNumberedProposal:bool)
//     requires
//         crequestbatch_is_valid(v),
//         forall |p:CPacket| S@.contains(p) ==> p.valid(),
//         COperationNumberIsValid(opn),
//         ({
//             forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
//         })
//     ensures
//     ({
//         let lr = LValIsHighestNumberedProposal(abstractify_crequestbatch(v), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
//         result_CValIsHighestNumberedProposal == lr
//     })
//     {
//         for p in S.iter() {
//             if let CMessage::CMessage1b { votes, .. } = &p.msg {
//                 if let Some(vote) = votes.v.get(&opn) {
//                     if Self::CValIsHighestNumberedProposalAtBallot(v.clone(), vote.max_value_bal, S.clone(), opn) {
//                         return true;
//                     }
//                 }
//             }
//         }
//         false
//     }

//     // #[verifier(external_body)]
//     pub fn CProposerCanNominateUsingOperationNumber(&self, log_truncation_point: COperationNumber, opn:COperationNumber) -> (result_CProposerCanNominateUsingOperationNumber:bool)
//     requires
//         self.valid(),
//         COperationNumberIsValid(log_truncation_point),
//         COperationNumberIsValid(opn),
//     ensures
//         ({
//             let lr = LProposerCanNominateUsingOperationNumber(self.view(), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCOperationNumberToOperationNumber(opn));
//             result_CProposerCanNominateUsingOperationNumber == lr
//         })
//     {
//         if self.current_state != 2 {
//             return false;
//         }

//         let quorum_size = self.constants.all.config.min_quorum_size();
//         let after_trunc = if opn.n >= self.max_log_truncation_point.n {
//             true
//         } else {
//             Self::CIsAfterLogTruncationPoint(opn, self.received_1b_packets.clone())
//         };
//         let sum = UpperBoundedAdditionImpl(
//             log_truncation_point.n,
//             self.constants.all.params.max_log_length,
//             self.constants.all.params.max_integer_val,
//         );

//         self.election_state.current_view == self.max_ballot_i_sent_1a
//             && self.current_state == 2
//             && self.received_1b_packets.len() as u64 >= quorum_size
//             && Self::CSetOfMessage1bAboutBallot(self.received_1b_packets.clone(), self.max_ballot_i_sent_1a)
//             && after_trunc
//             && opn.n < sum
//             && opn.n >= 0

//     }

//     // #[verifier(external_body)]
//     pub fn CProposerInit(c : CReplicaConstants)->(result_CProposerInit:CProposer)
//     requires
//         c.valid(),
//     ensures
//         result_CProposerInit.valid(),
//         LProposerInit(result_CProposerInit@, c@)
//     {
//         let election = CElectionState {
//             constants: c.clone(),
//             current_view: CBallot { seqno: 1, proposer_id: 0 },
//             current_view_suspectors: HashSet::new(),
//             epoch_end_time: 0,
//             epoch_length: c.all.params.baseline_view_timeout_period,
//             requests_received_this_epoch: Vec::new(),
//             requests_received_prev_epochs: Vec::new(),
//             cur_req_set: HashSet::new(),
//             prev_req_set: HashSet::new(),
//         };
//         let proposer = CProposer {
//             constants: c.clone(),
//             current_state: 0,
//             request_queue: Vec::new(),
//             max_ballot_i_sent_1a: CBallot { seqno: 0, proposer_id: c.my_index },
//             next_operation_number_to_propose: 0,
//             received_1b_packets: HashSet::new(),
//             highest_seqno_requested_by_client_this_view: HashMap::new(),
//             incomplete_batch_timer: CIncompleteBatchTimer::CIncompleteBatchTimerOff,
//             election_state: election,
//             max_opn_with_proposal: COperationNumber { n: 0 },
//             max_log_truncation_point: COperationNumber { n: 0 },
//         };

//         assert(proposer@.constants == c@);
//         assert(proposer@.current_state == 0);
//         assert(proposer@.request_queue == Seq::empty());
//         assert(proposer@.max_ballot_i_sent_1a == Ballot { seqno: 0, proposer_id: c@.my_index });
//         assert(proposer@.next_operation_number_to_propose == 0);
//         assert(proposer@.received_1b_packets == Set::empty());
//         assert(proposer@.highest_seqno_requested_by_client_this_view == Map::empty());
//         assert(proposer@.incomplete_batch_timer == IncompleteBatchTimer::IncompleteBatchTimerOff {});
//         assert(proposer@.election_state.constants == c@);

//         proposer

//     }

//     // #[verifier(external_body)]
//     pub fn CProposerProcessRequest(&mut self, packet:CPacket)
//     requires
//         old(self).valid(),
//         packet.valid(),
//         packet.msg is CMessageRequest
//     ensures
//         self.valid(),
//         LProposerProcessRequest(old(self)@, self@, packet@)
//     {
//         let CMessage::CMessageRequest { seqno, val } = packet.msg else { unreachable!() };
//         let val = CRequest { client: packet.src, seqno, request: val };
//         self.election_state.CElectionStateReflectReceivedRequest(val.clone());

//         if self.current_state != 0
//             && (!self.highest_seqno_requested_by_client_this_view.contains_key(&packet.src)
//                 || seqno > self.highest_seqno_requested_by_client_this_view[&packet.src])
//         {
//             self.highest_seqno_requested_by_client_this_view.insert(packet.src, seqno);
//             self.request_queue.push(val);
//         }
//     }

//     // #[verifier(external_body)]
//     pub fn CProposerMaybeEnterNewViewAndSend1a(&mut self) -> (result_CProposerMaybeEnterNewViewAndSend1a:OutboundPackets)
//     requires
//         old(self).valid(),
//     ensures
//         self.valid(),
//         result_CProposerMaybeEnterNewViewAndSend1a.valid(),
//         LProposerMaybeEnterNewViewAndSend1a(old(self)@, self@, result_CProposerMaybeEnterNewViewAndSend1a@)
//     {
//         let mut sent = OutboundPackets { packets: vec![] };

//         let quorum_size = self.constants.all.config.min_quorum_size();
//         if self.received_1b_packets.len() as u64 >= quorum_size && self.current_state == 1 {
//             let mut max_opn = COperationNumber { n: 0 };
//             let mut found_non_empty = false;
//             for p in self.received_1b_packets.iter() {
//                 if let CMessage::CMessage1b { votes, .. } = &p.msg {
//                     for (opn, _) in votes.v.iter() {
//                         if opn.n > max_opn.n {
//                             max_opn = *opn;
//                             found_non_empty = true;
//                         }
//                     }
//                 }
//             }
//             if found_non_empty && max_opn.n < 0xFFFF_FFFF_FFFF_FFFF {
//                 max_opn = COperationNumber { n: max_opn.n + 1 };
//             } else if !found_non_empty {
//                 max_opn = COperationNumber { n: 0 };
//             }

//             let mut max_log_tp = COperationNumber { n: 0 };
//             for p in self.received_1b_packets.iter() {
//                 if let CMessage::CMessage1b { log_truncation_point: ltp, .. } = &p.msg {
//                     if ltp.n > max_log_tp.n {
//                         max_log_tp = *ltp;
//                     }
//                 }
//             }

//             self.current_state = 2;
//             self.next_operation_number_to_propose = log_truncation_point.n;
//             self.max_opn_with_proposal = max_opn;
//             self.max_log_truncation_point = max_log_tp;

//             let msg = CMessage::CMessageStartingPhase2 {
//                 bal_starting_phase2: self.max_ballot_i_sent_1a,
//                 log_truncation_point,
//             };
//             for i in 0..self.constants.all.config.replica_ids.len() {
//                 let packet = CPacket {
//                     src: self.constants.all.config.replica_ids[self.constants.my_index as usize],
//                     dst: self.constants.all.config.replica_ids[i],
//                     msg,
//                 };
//                 sent.packets.push(packet);
//             }
//         }

//         sent
//     }

//     // #[verifier(external_body)]
//     pub fn CProposerNominateNewValueAndSend2a(&mut self, clock: u64, log_truncation_point: COperationNumber) -> (result_CProposerNominateNewValueAndSend2a:OutboundPackets)
//     requires
//         old(self).valid(),
//         COperationNumberIsValid(log_truncation_point),
//         // Self::CProposerCanNominateUsingOperationNumber(old(self), log_truncation_point, old(self).next_operation_number_to_propose),
//         // Self::CAllAcceptorsHadNoProposal(old(self).received_1b_packets, old(self).next_operation_number_to_propose),
//     ensures
//         self.valid(),
//         result_CProposerNominateNewValueAndSend2a.valid(),
//         LProposerNominateNewValueAndSend2a(old(self)@, self@, clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), result_CProposerNominateNewValueAndSend2a@)
//     {

//         let mut sent = OutboundPackets { packets: vec![] };
//         let batch_size = if self.request_queue.len() <= self.constants.all.params.max_batch_size as usize
//             || self.constants.all.params.max_batch_size < 0
//         {
//             self.request_queue.len()
//         } else {
//             self.constants.all.params.max_batch_size as usize
//         };

//         let v = self.request_queue[..batch_size].to_vec();
//         let opn = self.next_operation_number_to_propose;
//         let opn_op = COperationNumber { n: opn };
//         let clock_sum = UpperBoundedAdditionImpl(
//             clock,
//             self.constants.all.params.max_batch_delay,
//             self.constants.all.params.max_integer_val,
//         );
//         let new_timer = if self.request_queue.len() > batch_size {
//             CIncompleteBatchTimer::CIncompleteBatchTimerOn { when: clock_sum }
//         } else {
//             CIncompleteBatchTimer::CIncompleteBatchTimerOff
//         };

//         self.request_queue = self.request_queue[batch_size..].to_vec();
//         self.next_operation_number_to_propose = opn + 1;
//         self.incomplete_batch_timer = new_timer;

//         let msg = CMessage::CMessage2a {
//             bal_2a: self.max_ballot_i_sent_1a,
//             opn_2a: opn_op,
//             val_2a: v.clone(),
//         };
//         for i in 0..self.constants.all.config.replica_ids.len() {
//             let packet = CPacket {
//                 src: self.constants.all.config.replica_ids[self.constants.my_index as usize],
//                 dst: self.constants.all.config.replica_ids[i],
//                 msg: msg.clone(),
//             };
//             sent.packets.push(packet);
//         }

//         sent
//     }

//     pub fn CProposerMaybeNominateValueAndSend2a(&mut self, clock: u64, log_truncation_point: COperationNumber) -> (result: OutboundPackets)
//         requires
//             old(self).valid(),
//             COperationNumberIsValid(log_truncation_point),
//         ensures
//             self.valid(),
//             result.valid(),
//             LProposerMaybeNominateValueAndSend2a(old(self)@, self@, clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), result@),
//     {
//         let mut sent = OutboundPackets { packets: vec![] };

//         let opn_op = COperationNumber { n: self.next_operation_number_to_propose };
//         let can_nominate = self.CProposerCanNominateUsingOperationNumber(log_truncation_point, opn_op);
//         if !can_nominate {
//             return sent;
//         }

//         if self.next_operation_number_to_propose >= self.max_opn_with_proposal.n
//             && self.request_queue.is_empty()
//             && self.max_opn_with_proposal.n < 0xFFFF_FFFF_FFFF_FFFF
//         {
//             return sent;
//         }

//         let no_proposal = Self::CAllAcceptorsHadNoProposal(self.received_1b_packets.clone(), opn_op);
//         if !no_proposal {
//             sent = self.CProposerNominateOldValueAndSend2a(log_truncation_point);
//         } else {
//             let queue_size = self.request_queue.len();
//             let exists_opn = Self::CExistsAcceptorHasProposalLargeThanOpn(self.received_1b_packets.clone(), opn_op);

//             let timer_on = matches!(self.incomplete_batch_timer, CIncompleteBatchTimer::CIncompleteBatchTimerOn { .. });
//             let timer_expired = if let CIncompleteBatchTimer::CIncompleteBatchTimerOn { when } = self.incomplete_batch_timer {
//                 clock >= when
//             } else {
//                 false
//             };

//             if queue_size > 0 && timer_on && timer_expired
//                 || queue_size >= self.constants.all.params.max_batch_size as usize
//                 || exists_opn
//             {
//                 sent = self.CProposerNominateNewValueAndSend2a(clock, log_truncation_point);
//             } else if queue_size > 0 && !timer_on {
//                 let sum = UpperBoundedAdditionImpl(
//                     clock,
//                     self.constants.all.params.max_batch_delay,
//                     self.constants.all.params.max_integer_val,
//                 );
//                 self.incomplete_batch_timer = CIncompleteBatchTimer::CIncompleteBatchTimerOn { when: sum };
//             }
//         }

//         sent
//     }

//     // #[verifier(external_body)]
//     pub fn CProposerProcessHeartbeat(&mut self, p:CPacket, clock:u64)
//     requires
//         old(self).valid(),
//         p.valid(),
//         p.msg is CMessageHeartbeat,
//     ensures
//         self.valid(),
//         LProposerProcessHeartbeat(old(self)@, self@, p@, clock as int)
//     {
//         self.election_state.CElectionStateProcessHeartbeat(p.clone(), clock);

//         let old_view = old(self).election_state.current_view;
//         let new_view = self.election_state.current_view;
//         if CBalLt(old_view, new_view) {
//             self.current_state = 0;
//             self.request_queue.clear();
//         }
//     }

//     // #[verifier(external_body)]
//     pub fn CProposerCheckForViewTimeout(& mut self, clock:u64)
//     requires
//         old(self).valid(),
//     ensures
//         self.valid(),
//         LProposerCheckForViewTimeout(old(self)@, self@, clock as int)

//     {
//         self.election_state.CElectionStateCheckForViewTimeout(clock);
//     }

//     // #[verifier(external_body)]
//     pub fn CProposerCheckForQuorumOfViewSuspicions(&mut self, clock:u64)
//     requires
//         old(self).valid(),
//     ensures
//         self.valid(),
//         LProposerCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int)
//     {
//         let old_view = self.election_state.current_view;
//         self.election_state.CElectionStateCheckForQuorumOfViewSuspicions(clock);
//         let new_view = self.election_state.current_view;

//         if CBalLt(old_view, new_view) {
//             self.current_state = 0;
//             self.request_queue.clear();
//         }
//     }

//     // #[verifier(external_body)]
//     pub fn CProposerResetViewTimerDueToExecution(&mut self, val: CRequestBatch)
//     requires
//         old(self).valid(),
//         crequestbatch_is_valid(val),
//     ensures
//         self.valid(),
//         LProposerResetViewTimerDueToExecution(old(self)@, self@, abstractify_crequestbatch(val)),
//     {
//         self.election_state.ElectionStateReflectExecutedRequestBatch(val);
//     }

//     }
// }

use crate::common::collections::vecs::concat_vecs;
use crate::common::native::io_s::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::generic_refinement::*;
use crate::implementation::common::upper_bound::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::ElectionImpl::*;
use crate::protocol::common::upper_bound::*;
use crate::protocol::RSL::proposer::*;

use builtin::*;
use builtin_macros::*;
use std::collections::*;
use vstd::invariant;
use vstd::{map::*, prelude::*, seq::*, set::*};

verus! {

#[derive(Clone)]
pub enum CIncompleteBatchTimer{
    CIncompleteBatchTimerOn {when:u64},
    CIncompleteBatchTimerOff,
}

impl CIncompleteBatchTimer{

    pub open spec fn abstractable(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => true,
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => true,
        }
    }

    pub open spec fn valid(self) -> bool {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => self.abstractable(),
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => self.abstractable(),
        }
    }

    pub open spec fn view(self) -> IncompleteBatchTimer
        recommends
        self.abstractable(),
    {
        match self {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn {when} => IncompleteBatchTimer::IncompleteBatchTimerOn {when:when as int},
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => IncompleteBatchTimer::IncompleteBatchTimerOff{},
        }
    }

}

#[derive(Clone)]

pub struct CProposer {
    pub constants: CReplicaConstants,
    pub current_state: u64,
    pub request_queue: Vec<CRequest>,
    pub max_ballot_i_sent_1a: CBallot,
    pub next_operation_number_to_propose: u64,
    pub received_1b_packets: HashSet<CPacket>,
    pub highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64>,
    pub incomplete_batch_timer: CIncompleteBatchTimer,
    pub election_state: CElectionState,
}

impl CProposer{

    pub open spec fn abstractable(self) -> bool {
        &&& self.constants.abstractable()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].abstractable())
        &&& self.max_ballot_i_sent_1a.abstractable()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.abstractable())
        &&& (forall |k:EndPoint, v:u64| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.abstractable())
        &&& self.incomplete_batch_timer.abstractable()
        &&& self.election_state.abstractable()
    }

    pub open spec fn valid(self) -> bool {
        &&& self.abstractable()
        &&& self.constants.valid()
        &&& (forall |i:int| 0 <= i < self.request_queue@.len() ==> self.request_queue@[i].valid())
        &&& self.max_ballot_i_sent_1a.valid()
        &&& (forall |p:CPacket| self.received_1b_packets@.contains(p) ==> p.valid())
        &&& (forall |k:EndPoint, v:u64| self.highest_seqno_requested_by_client_this_view@.contains_key(k) ==> k.valid_public_key())
        &&& self.incomplete_batch_timer.valid()
        &&& self.election_state.valid()
    }

    pub open spec fn view(self) -> LProposer
    recommends self.valid(),
    {
        LProposer{
            constants: self.constants.view(),
            current_state: self.current_state as int,
            request_queue: self.request_queue@.map(|i, r:CRequest| r.view()),
            max_ballot_i_sent_1a: self.max_ballot_i_sent_1a.view(),
            next_operation_number_to_propose: self.next_operation_number_to_propose as int,
            received_1b_packets: self.received_1b_packets@.map(|p:CPacket| p.view()),
            highest_seqno_requested_by_client_this_view: Map::new(
                |ak: AbstractEndPoint| exists |k:EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak,
                |ak: AbstractEndPoint| {
                    let k = choose |k: EndPoint| self.highest_seqno_requested_by_client_this_view@.contains_key(k) && k@ == ak;
                    self.highest_seqno_requested_by_client_this_view@[k] as int
                }
            ),
            incomplete_batch_timer: self.incomplete_batch_timer.view(),
            election_state: self.election_state.view(),
        }
    }

    // #[verifier(external_body)]
    pub fn CIsAfterLogTruncationPoint(opn:COperationNumber, received_1b_packets:HashSet<CPacket>) -> bool
    {
        for p in &received_1b_packets {
            if let CMessage::CMessage1b { log_truncation_point, .. } = &p.msg {
                if log_truncation_point > &opn {
                    return false;
                }
        }
        }
        true
    }

    // #[verifier(external_body)]
    pub fn CSetOfMessage1b(S : HashSet<CPacket>) -> bool
    {
        for p in &S {
            if let CMessage::CMessage1b { .. } = &p.msg {
            }
            else {
                return false;
            }
        }
        true
    }

    // #[verifier(external_body)]
    pub fn CSetOfMessage1bAboutBallot(S:HashSet<CPacket>, b:CBallot) -> bool
    {
        for p in &S {
            match &p.msg {
                CMessage::CMessage1b { bal_1b,.. } => {
                    if *bal_1b != b {
                        return false;
                    }
                }
                _ => return false,
                }

            }
        true
    }

    // #[verifier(external_body)]
    pub fn CAllAcceptorsHadNoProposal(S:HashSet<CPacket>, opn:COperationNumber) -> (result_CAllAcceptorsHadNoProposal:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
        ({
            let lr = LAllAcceptorsHadNoProposal(S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
            result_CAllAcceptorsHadNoProposal == lr
        })
    {
        for p in &S {
            let CMessage::CMessage1b { votes, ..} = &p.msg else { unreachable!()};
            if votes.contains_key(&opn) {
                return false;
            }
        }
        true
    }

    // #[verifier(external_body)]
    pub fn CExistVotesHasProposalLargeThanOpn(p: CPacket, op: COperationNumber) -> (result_CExistVotesHasProposalLargeThanOpn:bool)
    requires
        p.valid(),
        COperationNumberIsValid(op),
        p.msg is CMessage1b
    ensures
    ({
        let lr = LExistVotesHasProposalLargeThanOpn(p.view(), AbstractifyCOperationNumberToOperationNumber(op));
        result_CExistVotesHasProposalLargeThanOpn == lr
    })
    {
        let CMessage:: CMessage1b { votes, ..} = &p.msg else { unreachable!()};
        for (&vote_opn, _) in votes.iter() {
            if vote_opn > op {
                return true;
            }
        }
        false
    }

    // #[verifier(external_body)]
    pub fn CExistsAcceptorHasProposalLargeThanOpn(S:HashSet<CPacket>, op:COperationNumber) -> (result_CExistsAcceptorHasProposalLargeThanOpn:bool)
    requires
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(op),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = LExistsAcceptorHasProposalLargeThanOpn(S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(op));
        result_CExistsAcceptorHasProposalLargeThanOpn == lr
    })

    {
        for pkt in &S {
            if Self::CExistVotesHasProposalLargeThanOpn(pkt.clone(), op) {
                return true;
            }
        }

        false
    }

    // #[verifier(external_body)]
    pub fn Cmax_balInS(c:CBallot, S:HashSet<CPacket>, opn:COperationNumber) -> (result_Cmax_balInS:bool)
    requires
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = Lmax_balInS(c.view(),S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_Cmax_balInS == lr
    })
    {
        for pkt in &S {
            let CMessage::CMessage1b { votes, ..} = &pkt.msg else { unreachable!()};
            if let Some(vote) = votes.get(&opn) {
                if !CBalLeq(&vote.max_value_bal, &c) {
                    return false;
                }
            }
        }
        true
    }

    // #[verifier(external_body)]
    pub fn CExistsBallotInS(v: CRequestBatch, c: CBallot, S: HashSet<CPacket>, opn:COperationNumber) -> (result_CExistsBallotInS:bool)
    requires
        crequestbatch_is_valid(v),
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = LExistsBallotInS(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CExistsBallotInS == lr
    })
    {
        for pkt in &S {
            let CMessage::CMessage1b { votes, ..} = &pkt.msg else { unreachable!()};

            if let Some(vote) =    votes.get(&opn) {
                if vote.max_value_bal == c  && vote.max_val == v {
                    return true;
                }
            }
        }
        false
    }

    // #[verifier(external_body)]
    pub fn CValIsHighestNumberedProposalAtBallot(v:CRequestBatch, c:CBallot, S:HashSet<CPacket>, opn:COperationNumber) -> (result_CValIsHighestNumberedProposalAtBallot:bool)
    requires
        crequestbatch_is_valid(v),
        c.valid(),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = LValIsHighestNumberedProposalAtBallot(abstractify_crequestbatch(v), c.view(), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CValIsHighestNumberedProposalAtBallot == lr
    })
    {
        if !Self::Cmax_balInS(c.clone(), S.clone(), opn) {
            return false;
        }
       return Self::CExistsBallotInS(v.clone(), c.clone(), S.clone(), opn);
    }
    // #[verifier(external_body)]
    pub fn CValIsHighestNumberedProposal(v: CRequestBatch, S: HashSet<CPacket>, opn:COperationNumber ) -> (result_CValIsHighestNumberedProposal:bool)
    requires
        crequestbatch_is_valid(v),
        forall |p:CPacket| S@.contains(p) ==> p.valid(),
        COperationNumberIsValid(opn),
        ({
            forall |p:CPacket| S@.contains(p) ==> p.msg is CMessage1b
        })
    ensures
    ({
        let lr = LValIsHighestNumberedProposal(abstractify_crequestbatch(v), S@.map(|p:CPacket| p.view()), AbstractifyCOperationNumberToOperationNumber(opn));
        result_CValIsHighestNumberedProposal == lr
    })
    {
        for pkt in &S {
            // Destructure the 1b message to get its votes map
            let CMessage::CMessage1b { votes, .. } = &pkt.msg else { unreachable!() };
            // If this acceptor voted at slot `opn`...
            if let Some(cv) = votes.get(&opn) {
                let c = cv.max_value_bal.clone();
                if Self::CValIsHighestNumberedProposalAtBallot(
                    v.clone(), c.clone(), S.clone(), opn
                ) {
                    return true;
                }
            }
        }
        false
    }

    // #[verifier(external_body)]
    pub fn CProposerCanNominateUsingOperationNumber(&self, log_truncation_point: COperationNumber, opn:COperationNumber) -> (result_CProposerCanNominateUsingOperationNumber:bool)
    requires
        self.valid(),
        COperationNumberIsValid(log_truncation_point),
        COperationNumberIsValid(opn),
    ensures
        ({
            let lr = LProposerCanNominateUsingOperationNumber(self.view(), AbstractifyCOperationNumberToOperationNumber(log_truncation_point), AbstractifyCOperationNumberToOperationNumber(opn));
            result_CProposerCanNominateUsingOperationNumber == lr
        })
    {
        let cond1 = self.election_state.current_view == self.max_ballot_i_sent_1a.clone();

        // 2) And in phase-2 (state == 2)
        let cond2 = self.current_state == 2;

        // 3) And we have at least a quorum of 1b’s
        let q = self.constants.all.config.CMinQuorumSize();
        let cond3 = self.received_1b_packets.len() >= q;

        // 4) And all those 1b’s are about that ballot
        let cond4 = Self::CSetOfMessage1bAboutBallot(
            self.received_1b_packets.clone(),
            self.max_ballot_i_sent_1a.clone(),
        );

        // 5) And none of those acceptors has truncated past opn
        let cond5 = Self::CIsAfterLogTruncationPoint(opn.clone(),
            self.received_1b_packets.clone()
        );

        // 6) And opn is strictly less than log_truncation_point + max_log_length
        let ub = CUpperBoundedAddition(
            log_truncation_point,
            self.constants.all.params.max_log_length,
            self.constants.all.params.max_integer_val,
        );
        let cond6 = opn < ub;

        // 7) Unsigned opn ≥ 0 is always true, so we can omit that check.

        // 8) And opn itself plus one must stay below the max_integer_val
        let cond7 = opn < self.constants.all.params.max_integer_val;

        cond1 && cond2 && cond3 && cond4 && cond5 && cond6 && cond7
    }

    // #[verifier(external_body)]
    pub fn CProposerInit(c : CReplicaConstants)->(result_CProposerInit:CProposer)
    requires
        c.valid(),
    ensures
        result_CProposerInit.valid(),
        LProposerInit(result_CProposerInit@, c@)
    {
        let constants = c;
        // 2. start out not leader
        let current_state = 0_u64;
        // 3. empty client request queue
        let request_queue: Vec<CRequest> = Vec::new();
        // 4. initial ballot (0, my_index)
        let max_ballot_i_sent_1a = CBallot {
            seqno: 0,
            proposer_id: constants.my_index as u64,
        };
        // 5. next opn to propose = 0
        let next_operation_number_to_propose = 0_u64;
        // 6. no 1b’s received yet
        let received_1b_packets: HashSet<CPacket> = HashSet::new();
        // 7. highest seqno per client = empty
        let highest_seqno_requested_by_client_this_view: HashMap<EndPoint, u64> = HashMap::new();
        // 8. incomplete‐batch timer off
        let incomplete_batch_timer = CIncompleteBatchTimer::CIncompleteBatchTimerOff;
        // 9. election state initialized
        let election_state = CElectionState::CElectionStateInit(constants.clone());

        let cp = CProposer {
            constants,
            current_state,
            request_queue,
            max_ballot_i_sent_1a,
            next_operation_number_to_propose,
            received_1b_packets,
            highest_seqno_requested_by_client_this_view,
            incomplete_batch_timer,
            election_state,
        };



        let ghost sp = cp@;
        let ghost cc = c@;

        assert(sp.constants == cc);
        assert(sp.current_state == 0);
        assert(sp.request_queue.len() == 0);
        assert(sp.max_ballot_i_sent_1a == CBallot { seqno: 0, proposer_id: cc.my_index });
        assert(sp.next_operation_number_to_propose == 0);
        assert(sp.received_1b_packets.len() == 0);
        assert(sp.highest_seqno_requested_by_client_this_view.dom().is_empty());
        assert(CElectionState::CElectionStateInit(sp.election_state.clone()));
        assert(sp.incomplete_batch_timer.IncompleteBatchTimerOff?);

        cp


    }

    // #[verifier(external_body)]
    pub fn CProposerProcessRequest(&mut self, packet:CPacket)
    requires
        old(self).valid(),
        packet.valid(),
        packet.msg is CMessageRequest
    ensures
        self.valid(),
        LProposerProcessRequest(old(self)@, self@, packet@)
    {
        let CMessage::CMessageRequest { seqno_req, val } = packet.msg else { unreachable!() };
        let client = packet.src;
        let req = CRequest { client, seqno: seqno_req, request: val.clone_up_to_view() };
        self.election_state.CElectionStateReflectReceivedRequest(req.clone());
        if self.current_state != 0 {
            let prev = self
                .highest_seqno_requested_by_client_this_view
                .get(&req.client)
                .copied()
                .unwrap_or(0);
            if req.seqno > prev {
                self.request_queue.push(req.clone());
                self.highest_seqno_requested_by_client_this_view
                    .insert(req.client, req.seqno);
            }
        }
    }
    // #[verifier(external_body)]
    pub fn CProposerMaybeEnterNewViewAndSend1a(&mut self) -> (result_CProposerMaybeEnterNewViewAndSend1a:OutboundPackets)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        result_CProposerMaybeEnterNewViewAndSend1a.valid(),
        LProposerMaybeEnterNewViewAndSend1a(old(self)@, self@, result_CProposerMaybeEnterNewViewAndSend1a@)
    {
        let mut out = OutboundPackets::PacketSequence { s: Vec::new() };
        let view_bal = self.election_state.current_view.clone_up_to_view();

        if view_bal.proposer_id == self.constants.my_index
           && CBalLt(&self.max_ballot_i_sent_1a, &view_bal)
        {
            // 1: Transition into phase 1
            self.current_state = 1;
            self.max_ballot_i_sent_1a = view_bal.clone_up_to_view();
            self.received_1b_packets.clear();
            self.highest_seqno_requested_by_client_this_view.clear();
            // 2: Rebuild the request queue from election history
            let mut new_q = self.election_state.requests_received_prev_epochs.clone();
            new_q.extend(self.election_state.requests_received_this_epoch.clone());
            self.request_queue = new_q;
            let bc = CBroadcast::BuildBroadcastToEveryone(
                self.constants.all.config.clone(),
                self.constants.my_index,
                CMessage::CMessage1a { bal_1a: view_bal.clone_up_to_view() }
            );
            out = OutboundPackets::Broadcast { broadcast: bc };
        }
        out

    }

    // #[verifier(external_body)]
    pub fn CProposerProcess1b(&mut self, p: CPacket)
    requires
        old(self).valid(),
        p.valid(),
        p.msg is CMessage1b,
    ensures
        self.valid(),
        LProposerProcess1b(old(self)@, self@, p@)
    {
        self.received_1b_packets.insert(p);
    }

    // #[verifier(external_body)]
    pub fn CProposerMaybeEnterPhase2(&mut self, log_truncation_point: COperationNumber) -> (result: OutboundPackets)
    requires
        old(self).valid(),
        COperationNumberIsValid(log_truncation_point),
    ensures
        self.valid(),
        result.valid(),
        LProposerMaybeEnterPhase2(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), result@)
    {
        let q = self.constants.all.config.CMinQuorumSize();
        if self.received_1b_packets.len() >= q
            && Self::CSetOfMessage1bAboutBallot(self.received_1b_packets.clone(), self.max_ballot_i_sent_1a.clone_up_to_view())
            && self.current_state == 1
        {
            self.current_state = 2;
            self.next_operation_number_to_propose = log_truncation_point;
            let msg = CMessage::CMessageStartingPhase2 {
                bal_2: self.max_ballot_i_sent_1a.clone_up_to_view(),
                logTruncationPoint_2: log_truncation_point,
            };
            let bc = CBroadcast::BuildBroadcastToEveryone(
                self.constants.all.config.clone(),
                self.constants.my_index as u64,
                msg,
            );
            OutboundPackets::Broadcast { broadcast: bc }
        } else {
            OutboundPackets::PacketSequence { s: Vec::new() }
        }
    }

    // #[verifier(external_body)]
    pub fn CProposerNominateNewValueAndSend2a(&mut self, clock: u64, log_truncation_point: COperationNumber) -> (result_CProposerNominateNewValueAndSend2a:OutboundPackets)
    requires
        old(self).valid(),
        COperationNumberIsValid(log_truncation_point),
        // Self::CProposerCanNominateUsingOperationNumber(old(self), log_truncation_point, old(self).next_operation_number_to_propose),
        // Self::CAllAcceptorsHadNoProposal(old(self).received_1b_packets, old(self).next_operation_number_to_propose),
    ensures
        self.valid(),
        result_CProposerNominateNewValueAndSend2a.valid(),
        LProposerNominateNewValueAndSend2a(old(self)@, self@, clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), result_CProposerNominateNewValueAndSend2a@)
    {
        let max_bs = self.constants.all.params.max_batch_size as usize;
        let rq_len = self.request_queue.len();
        let batch_size = if max_bs == 0 || rq_len <= max_bs {
            rq_len
        } else {
            max_bs
        };

        let v: CRequestBatch = self.request_queue[..batch_size].to_vec();
        let opn = self.next_operation_number_to_propose;
        self.request_queue = self.request_queue[batch_size..].to_vec();
        self.next_operation_number_to_propose = opn + 1;
        self.incomplete_batch_timer = if self.request_queue.len() > batch_size {
            let when = CUpperBoundedAddition(
                clock,
                self.constants.all.params.max_batch_delay,
                self.constants.all.params.max_integer_val,
            );
            CIncompleteBatchTimer::CIncompleteBatchTimerOn { when }
        } else {
            CIncompleteBatchTimer::CIncompleteBatchTimerOff
        };
        let msg = CMessage::CMessage2a {
            bal_2a: self.max_ballot_i_sent_1a.clone_up_to_view(),
            opn_2a: opn,
            val_2a: v.clone(),
        };
        let bc = CBroadcast::BuildBroadcastToEveryone(
            self.constants.all.config.clone(),
            self.constants.my_index as u64,
            msg.clone(),
            );
        OutboundPackets::Broadcast { broadcast: bc }

    }

    // #[verifier(external_body)]
    pub fn CProposerNominateOldValueAndSend2a(&mut self, log_truncation_point: COperationNumber) -> (result: OutboundPackets)
    requires
        old(self).valid(),
        COperationNumberIsValid(log_truncation_point),
    ensures
        self.valid(),
        result.valid(),
        LProposerNominateOldValueAndSend2a(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), result@)
    {
        let opn = self.next_operation_number_to_propose;

        // Find the highest-numbered proposal at this operation number
        let mut highest_bal: Option<CBallot> = None;
        let mut highest_val: CRequestBatch = Vec::new();

        for pkt in &self.received_1b_packets {
            let CMessage::CMessage1b { votes, .. } = &pkt.msg else { continue };
            if let Some(vote) = votes.get(&opn) {
                let should_update = match &highest_bal {
                    None => true,
                    Some(hb) => CBalLt(hb, &vote.max_value_bal),
                };
                if should_update {
                    highest_bal = Some(vote.max_value_bal.clone_up_to_view());
                    highest_val = vote.max_val.clone();
                }
            }
        }

        self.next_operation_number_to_propose = opn + 1;

        let msg = CMessage::CMessage2a {
            bal_2a: self.max_ballot_i_sent_1a.clone_up_to_view(),
            opn_2a: opn,
            val_2a: highest_val,
        };
        let bc = CBroadcast::BuildBroadcastToEveryone(
            self.constants.all.config.clone(),
            self.constants.my_index as u64,
            msg,
        );
        OutboundPackets::Broadcast { broadcast: bc }
    }

    // #[verifier(external_body)]
    pub fn CProposerMaybeNominateValueAndSend2a(&mut self, clock: u64, log_truncation_point: COperationNumber) -> (result: OutboundPackets)
    requires
        old(self).valid(),
        COperationNumberIsValid(log_truncation_point),
    ensures
        self.valid(),
        result.valid(),
        LProposerMaybeNominateValueAndSend2a(old(self)@, self@, clock as int, AbstractifyCOperationNumberToOperationNumber(log_truncation_point), result@)
    {
        let opn = self.next_operation_number_to_propose;
        let can_nominate = self.CProposerCanNominateUsingOperationNumber(log_truncation_point, opn);

        if !can_nominate {
            return OutboundPackets::PacketSequence { s: Vec::new() };
        }

        let no_proposal = Self::CAllAcceptorsHadNoProposal(self.received_1b_packets.clone(), opn);

        if !no_proposal {
            return self.CProposerNominateOldValueAndSend2a(log_truncation_point);
        }

        let exists_higher = Self::CExistsAcceptorHasProposalLargeThanOpn(self.received_1b_packets.clone(), opn);

        let queue_len = self.request_queue.len();
        let max_bs = self.constants.all.params.max_batch_size as usize;

        let timer_expired = match &self.incomplete_batch_timer {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn { when } => clock >= *when,
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => false,
        };

        if exists_higher
            || queue_len >= max_bs
            || (queue_len > 0 && timer_expired)
        {
            return self.CProposerNominateNewValueAndSend2a(clock, log_truncation_point);
        }

        let timer_off = match &self.incomplete_batch_timer {
            CIncompleteBatchTimer::CIncompleteBatchTimerOn { .. } => false,
            CIncompleteBatchTimer::CIncompleteBatchTimerOff => true,
        };

        if queue_len > 0 && timer_off {
            let when = CUpperBoundedAddition(
                clock,
                self.constants.all.params.max_batch_delay,
                self.constants.all.params.max_integer_val,
            );
            self.incomplete_batch_timer = CIncompleteBatchTimer::CIncompleteBatchTimerOn { when };
            return OutboundPackets::PacketSequence { s: Vec::new() };
        }

        OutboundPackets::PacketSequence { s: Vec::new() }
    }

    // #[verifier(external_body)]
    pub fn CProposerProcessHeartbeat(&mut self, p:CPacket, clock:u64)
    requires
        old(self).valid(),
        p.valid(),
        p.msg is CMessageHeartbeat,
    ensures
        self.valid(),
        LProposerProcessHeartbeat(old(self)@, self@, p@, clock as int)
    {
        self.election_state.CElectionStateProcessHeartbeat(p.clone(), clock);
        let new_view = self.election_state.current_view.clone_up_to_view();
        let old_view = self.max_ballot_i_sent_1a.clone_up_to_view();
        if CBalLt(&old_view, &new_view) {
            self.current_state = 0;
            self.request_queue.clear();
        }
    }
    // #[verifier(external_body)]
    pub fn CProposerCheckForViewTimeout(& mut self, clock:u64)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        LProposerCheckForViewTimeout(old(self)@, self@, clock as int)

    {
        self.election_state.CElectionStateCheckForViewTimeout(clock);
    }

    // #[verifier(external_body)]
    pub fn CProposerCheckForQuorumOfViewSuspicions(&mut self, clock:u64)
    requires
        old(self).valid(),
    ensures
        self.valid(),
        LProposerCheckForQuorumOfViewSuspicions(old(self)@, self@, clock as int)
    {
        let old_view = self.election_state.current_view.clone_up_to_view();
        self.election_state.CElectionStateCheckForQuorumOfViewSuspicions(clock);
        let new_view = self.election_state.current_view.clone_up_to_view();
        if CBalLt(&old_view, &new_view) {
            self.current_state = 0;
            self.request_queue.clear();
        }
    }

    // #[verifier(external_body)]
    pub fn CProposerResetViewTimerDueToExecution(&mut self, val: CRequestBatch)
    requires
        old(self).valid(),
        crequestbatch_is_valid(val),
    ensures
        self.valid(),
        LProposerResetViewTimerDueToExecution(old(self)@, self@, abstractify_crequestbatch(val)),
    {
        self.election_state.ElectionStateReflectExecutedRequestBatch(val);
    }

    }
}
