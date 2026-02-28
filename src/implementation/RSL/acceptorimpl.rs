use super::types_i::COperationNumber;
use builtin::*;
use builtin_macros::*;
use std::collections::HashMap;
use std::{result, vec};
use vstd::rwlock::RwLockToks::Config;
use vstd::{invariant, map::*, prelude::*, seq::*};

use crate::common::collections::*;
use crate::common::collections::{count_matches::*, maps::*, vecs::*};
use crate::common::{collections::maps::*, native::io_s::EndPoint};
use crate::implementation::common::{generic_refinement::*, upper_bound::*};
use crate::implementation::RSL::cbroadcast::OutboundPackets;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::types_i::CBalLt;
use crate::implementation::RSL::{
    cbroadcast::*, cconfiguration::*, cconstants::*, cmessage::*, types_i::*,
};
use crate::protocol::RSL::{acceptor::*, environment::*, message::*, types::*};
// option ­A – import just the one item you need
use crate::common::collections::count_matches::*;
// use crate::protocol::RSL::configuration::LMinQuorumSize;

// option ­B – import the whole module then qualify when you call
// use crate::common::collections::count_matches;

verus! {

    #[verifier(external_body)]
    fn is_nth_highest_value_in_sequence(value: COperationNumber, seq: &Vec<COperationNumber>, n: usize) -> bool {
        if n == 0 || n >= seq.len() { return false; }
        let mut contains = false;
        let mut i: usize = 0;
        while i < seq.len() {
            if seq[i] == value { contains = true; break; }
            i += 1;
        }
        if !contains { return false; }
        let mut greater_count: usize = 0;
        let mut ge_count: usize = 0;
        let mut j: usize = 0;
        while j < seq.len() {
            if seq[j] > value { greater_count += 1; }
            if seq[j] >= value { ge_count += 1; }
            j += 1;
        }
        greater_count < n && ge_count >= n
    }

    // Datatype for CAcceptor
    #[derive(Clone)]
    pub struct CAcceptor {
        pub constants: CReplicaConstants,
        pub max_bal: CBallot,
        pub votes: CVotes,
        pub last_checkpointed_operation: Vec<COperationNumber>,
        pub log_truncation_point: COperationNumber,
        pub min_voted_opn : COperationNumber,
    }

    impl CAcceptor{
        pub open spec fn abstractable(self) -> bool
        {
            &&& self.constants.abstractable()
            &&& self.max_bal.abstractable()
            &&& cvotes_is_abstractable(self.votes)
            &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsAbstractable(self.last_checkpointed_operation[i]))
            &&& COperationNumberIsAbstractable(self.log_truncation_point)
        }

        // Predicate to check if CAcceptor is valid
        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            &&& self.constants.valid()
            &&& self.max_bal.valid()
            &&& cvotes_is_valid(self.votes)
            &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsValid(self.last_checkpointed_operation[i]))
            &&& COperationNumberIsValid(self.log_truncation_point)
            &&& self.last_checkpointed_operation.len() == self.constants.all.config.replica_ids.len()
        }

        // Function to abstractify CAcceptor to LAcceptor
        pub open spec fn view(self) -> LAcceptor
            recommends self.abstractable()
        {
            LAcceptor {
                constants: self.constants.view(),
                max_bal: self.max_bal.view(),
                votes: abstractify_cvotes(self.votes),
                last_checkpointed_operation:self.last_checkpointed_operation@.map(|i,c:COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
                log_truncation_point: AbstractifyCOperationNumberToOperationNumber(self.log_truncation_point),
            }
        }



        #[verifier(external_body)]
        pub fn CIsLogTruncationPointValid(log_truncation_point: COperationNumber, last_checkpointed_operation: Vec<COperationNumber>, config: CConfiguration) -> (isValid :bool)
            requires
                COperationNumberIsValid(log_truncation_point),
                forall|i:int| 0<=i<=last_checkpointed_operation.len() | last_checkpointed_operation[i] as usize ==> COperationNumberIsValid(last_checkpointed_operation[i]),
                config.valid()
            ensures
                isValid == IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),
                last_checkpointed_operation@.map(|i,c:COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
                config.view())
        {
            is_nth_highest_value_in_sequence(log_truncation_point, &last_checkpointed_operation, config.CMinQuorumSize())

     }

        #[verifier(external_body)]
        pub fn CRemoveVotesBeforeLogTruncationPoint(votes: CVotes, log_truncation_point: COperationNumber) -> (cvotes:CVotes)
            requires
                cvotes_is_valid(votes),
                COperationNumberIsValid(log_truncation_point),
            ensures
            cvotes_is_valid(cvotes) && RemoveVotesBeforeLogTruncationPoint(abstractify_cvotes(cvotes), abstractify_cvotes(votes), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
        {
        //   let mut cvotes = votes.clone();
        //   &&& (forall|opn :COperationNumber| cvotes.contains_key(&opn)==> votes.contains_key(&opn) && cvotes[opn] === votes[opn])
        //   &&& (forall|opn :COperationNumber| (opn as int) < log_truncation_point ==> !cvotes.contains_key(&opn))
        //   &&& (forall|opn :COperationNumber| (opn as int) >= log_truncation_point ==> !cvotes.contains_key(&opn) ==> cvotes.contains_key(&opn))
        //   &&& cvotes.dom().subset_of(votes.dom())
        //   &&& (forall |opn :COperationNumber| cvotes.contains_key(&opn) ==> (opn as int) >= log_truncation_point)
        let mut cvotes = votes.clone();
        // keep only entries whose opn ≥ the truncation point
        cvotes.retain(|opn, _vote| *opn >= log_truncation_point);
        cvotes

        }

        #[verifier(external_body)]
        pub fn CAddVoteAndRemoveOldOnes(votes: CVotes, new_opn: COperationNumber, new_vote: CVote, log_truncation_point: COperationNumber) -> (cvotes_2:CVotes)
            requires
                cvotes_is_valid(votes),
                COperationNumberIsValid(new_opn),
                new_vote.valid(),
                COperationNumberIsValid(log_truncation_point),
            ensures
                cvotes_is_valid(cvotes_2) && LAddVoteAndRemoveOldOnes(abstractify_cvotes(votes), abstractify_cvotes(cvotes_2), AbstractifyCOperationNumberToOperationNumber(new_opn), new_vote.view(), AbstractifyCOperationNumberToOperationNumber(log_truncation_point))
        {
            let mut cvotes_2 = votes.clone();
            cvotes_2.retain(|opn,_| *opn >= log_truncation_point);
            if new_opn >= log_truncation_point {
                cvotes_2.insert(new_opn, new_vote);
            }
            cvotes_2
        }


        pub fn CAcceptorInit(c: CReplicaConstants) -> (rc:Self)
            requires c.valid()
            ensures
                rc.valid(),
                LAcceptorInit(
                    rc@, /* used to convert the implementation type to protocol type */
                    c@
                ) /* refinement condition */
        {

            // let t2 = CBallot{
            //     seqno: 0,
            //     proposer_id: 0,
            // };
            // let t3: HashMap<COperationNumber,CVote> = HashMap::new();

            // let len = c.all.config.replica_ids.len();
            // let mut t4: Vec<u64> = Vec::new();
            // let mut i = 0;
            // while i < len
            //     invariant
            //         i <= len,
            //         t4.len() == i,
            //         forall |j:int| 0 <= j < i ==> t4[j] == 0,
            // {
            //     t4.push(0);
            //     i = i + 1;
            // }

            // assert(t4.len() == len);
            // assert(forall |idx:int| 0 <= idx < t4.len() ==> t4[idx] == 0);

            // let t5 = 0;

            // let s = CAcceptor{constants:c, max_bal:t2, votes:t3, last_checkpointed_operation:t4, log_truncation_point:t5};

            // let ghost ss = s@;
            // let ghost sc = c@;

            // assert(ss.constants == sc);
            // assert(ss.max_bal == Ballot{seqno:0,proposer_id:0});
            // assert(ss.votes == Map::<OperationNumber, Vote>::empty());
            // assert(ss.last_checkpointed_operation.len() == sc.all.config.replica_ids.len());
            // assert(forall |idx:int| 0 <= idx < ss.last_checkpointed_operation.len() ==> ss.last_checkpointed_operation[idx] == 0);
            // assert(ss.log_truncation_point == 0);

            // s
            let zero_bal = CBallot { seqno: 0, proposer_id: 0 };
            let empty_votes = CVotes::new();
            let len = c.all.config.replica_ids.len();
            let mut last_chk: Vec<COperationNumber> = Vec::new();

            let mut i = 0;
            while i < len
                invariant
                    i <= len,
                    last_chk.len() == i,
                    forall |j: int| 0 <= j && j < i ==> last_chk[j] == 0,
            {
                last_chk.push(0);
                i = i + 1;
            }
            assert(last_chk.len() == len);
            assert(forall |j: int| 0 <= j && j < len ==> last_chk[j] == 0);

            let rc = CAcceptor {
                constants: c,
                max_bal: zero_bal,
                votes: empty_votes,
                last_checkpointed_operation: last_chk,
                log_truncation_point: 0,
                min_voted_opn: 0,
            };

            let ghost ss = rc@;
            let ghost cc = c@;
            assert(ss.constants == cc);
            assert(ss.max_bal == Ballot { seqno: 0, proposer_id: 0 });
            assert(ss.votes == Map::<OperationNumber, Vote>::empty());
            assert(ss.last_checkpointed_operation.len() == cc.all.config.replica_ids.len());
            assert(forall |idx: int|
                       0 <= idx && idx < ss.last_checkpointed_operation.len() ==>
                       ss.last_checkpointed_operation[idx] == 0);
            assert(ss.log_truncation_point == 0);


            rc
        }

        #[verifier(external_body)]
        pub fn CAcceptorProcess1a(&mut self, inp: CPacket) -> (sent: OutboundPackets)
            requires
                old(self).valid(),
                inp.valid(),
                inp.msg is CMessage1a
            ensures
                self.valid(),
                sent.valid(),
                LAcceptorProcess1a(old(self)@, self@, inp@, sent@) /* this is the refinement obligation */
        {
            // let mut sent = OutboundPackets { packets: vec![] };
            // let CMessage::CMessage1a { bal_1a } = inp.msg else { unreachable!() };
            // let sender = inp.src;
            // if !CBalLt(self.max_bal, bal_1a) || !self.constants.all.config.replica_ids.contains(&sender) {
            //     return sent;
            // }
            // self.max_bal = bal_1a;
            // let msg_1b = CMessage::CMessage1b {
            //     bal_1b: bal_1a,
            //     log_truncation_point: self.log_truncation_point,
            //    votes : self.votes.clone(),
            // };
            // let packet = CPacket {
            //     src: self.constants.all.config.replica_ids[self.constants.my_index as usize],
            //     dst: sender,
            //     msg: msg_1b,
            // };
            // sent.packets.push(packet);
            // sent

            let mut sent = OutboundPackets::PacketSequence { s: Vec::new()};
            let CMessage::CMessage1a { bal_1a } = inp.msg else { unreachable!() };
            let sender = inp.src;
             if !CBalLt(&self.max_bal, &bal_1a)
                || !self.constants.all.config.replica_ids.contains(&sender)
            {
                return sent;
            }
            self.max_bal = bal_1a.clone();

            let reply = CPacket {
                src: self.constants.all.config.replica_ids[self.constants.my_index as usize].clone(),
                dst: sender,
                msg: CMessage::CMessage1b {
                    bal_1b: bal_1a.clone(),
                    log_truncation_point: self.log_truncation_point.clone(),
                    votes: self.votes.clone(),
                },
            };
            if let OutboundPackets::PacketSequence { ref mut s } = sent {
                s.push(reply);
            }

            sent
        }
        #[verifier(external_body)]
        pub fn CAcceptorProcess2a(&mut self, inp:CPacket) -> (sent:OutboundPackets)
            requires
                old(self).valid(),
                inp.valid(),
                inp.msg is CMessage2a,
            ensures
                self.valid(),
                LAcceptorProcess2a(old(self)@, self@, inp@, sent@)
        {
        //     let mut sent = OutboundPackets { packets: vec![] };
        //     let CMessage::CMessage2a {bal_2a,opn_2a,val_2a} = inp.msg else { unreachable!() };
        //     let sender = inp.src;
        //     if CBalLt(&bal_2a,&self.max_bal) || opn_2a.n > self.constants.all.params.max_integer_val || !self.constants.all.config.replica_ids.contains(&sender) {
        //         return sent;
        //     }
        //     let max_log_len = self.constants.all.params.max_log_length;
        //     let mut new_log_truncation_point = self.log_truncation_point;
        //     if opn_2a.n >= max_log_len -1 {
        //         let potetial_new_trucation = opn_2a.n -(max_log_len -1);
        //         if potetial_new_trucation > self.log_truncation_point.n {
        //             new_log_truncation_point = COperationNumber {n : potetial_new_trucation};
        //         }
        //     }
        //     if opn_2a.n >= self.log_truncation_point.n {
        //         let new_votes = CVote { max_bal: bal_2a, val: val_2a };
        //         self.votes = self.CAddVoteAndRemoveOldOnes(self.votes.clone(), opn_2a, new_votes, new_log_truncation_point);

        // }
        // self.max_bal = bal_2a;
        // self.log_truncation_point = new_log_truncation_point;

        // let msf_2b = Cmessage::CMessage2b {
        //     bal_2a: bal_2a,
        //     opn_2b: opn_2a,
        //     val_2b: val_2a,

        // };
        // for i in 0..self.constants.all.config.replica_ids.len(){
        //     let packet = CPacket {
        //         src: self.constants.all.config.replica_ids[self.constants.my_index as usize],
        //         dst : self.constants.all.config.replica_ids[i],
        //         msg : msf_2b.clone(),
        //     };
        //     sent.packets.push(packet);
        // }
        // sent
        let mut sent = OutboundPackets::PacketSequence { s: vec![] };

        let CMessage::CMessage2a { bal_2a, opn_2a, val_2a } = inp.msg else { unreachable!() };
        let sender = inp.src;

        if CBalLt(&bal_2a, &self.max_bal)
            || opn_2a > self.constants.all.params.max_integer_val
            || !self.constants.all.config.replica_ids.contains(&sender)
        {
            return sent;
        }

        let max_len = self.constants.all.params.max_log_length;
        let mut new_trunc = self.log_truncation_point;
            if opn_2a >= max_len.saturating_sub(1) {
                let candidate = opn_2a - (max_len - 1);
                if candidate > new_trunc {
                    new_trunc = candidate;
                }
            }
            if self.log_truncation_point <= opn_2a {
                let cv = CVote {
                    max_value_bal: bal_2a.clone(),
                    max_val: val_2a.clone(),
                };
                self.votes = Self::CAddVoteAndRemoveOldOnes(
                    self.votes.clone(),
                    opn_2a,
                    cv,
                    new_trunc,
                );
            }
                self.max_bal = bal_2a.clone();
                self.log_truncation_point = new_trunc;


                let reply = CMessage::CMessage2b {
                    bal_2b: bal_2a,
                    opn_2b: opn_2a,
                    val_2b: val_2a,
                };
                if let OutboundPackets::PacketSequence { ref mut s } = sent {
                    for dst in self.constants.all.config.replica_ids.clone() {
                        s.push(CPacket {
                            src: self.constants.all.config.replica_ids[self.constants.my_index as usize].clone(),
                            dst,
                            msg: reply.clone(),
                        });
                    }
                }
            sent
        }


        #[verifier(external_body)]
        pub fn CAcceptorProcessHeartbeat(&mut self, inp: CPacket)
            requires
                old(self).valid(),
                inp.valid(),
                inp.msg is CMessageHeartbeat,
            ensures
                self.valid(),
                LAcceptorProcessHeartbeat(old(self)@, self@, inp@)
        {
            // let CMessage::CMessageHeartbeat { opn_ckpt, .. } = inp.msg else { unreachable!() };
            // let sender = inp.src;

            // let mut found = false;
            // let mut index = 0;
            // for i in 0..self.constants.all.config.replica_ids.len() {
            //     if self.constants.all.config.replica_ids[i] == sender {
            //         found = true;
            //         index = i;
            //         break;
            //     }
            // }
            // if !found || opn_ckpt.n <= self.last_checkpointed_operation[index].n {
            //     return;
            // }
            // self.last_checkpointed_operation[index] = opn_ckpt;


            let CMessage::CMessageHeartbeat { opn_ckpt,.. } = inp.msg else { unreachable!() };
            let sender = inp.src;

            if let Some(idx) = self
                .constants
                .all
                .config
                .replica_ids
                .iter()
                .position(|id| id == &sender)
            {
                if opn_ckpt > self.last_checkpointed_operation[idx] {
                    self.last_checkpointed_operation[idx] = opn_ckpt;
                }
            }

        }

        #[verifier(external_body)]
        pub fn CAcceptorTruncateLog(&mut self, opn: COperationNumber)
            requires
                old(self).valid(),
                COperationNumberIsValid(opn)
            ensures
                self.valid(),
                LAcceptorTruncateLog(old(self)@, self@, AbstractifyCOperationNumberToOperationNumber(opn))
        {
            // if opn.n <= Self.log_truncation_point.n {
            //     return;
            // }
            // self.votes = Self.CRemoveVotesBeforeLogTruncationPoint(self.votes.clone(), opn);
            // self.log_truncation_point = opn;

            if opn > self.log_truncation_point {
                self.votes = Self::CRemoveVotesBeforeLogTruncationPoint(self.votes.clone(), opn);
                self.log_truncation_point = opn;
            }

        }

    }
}
