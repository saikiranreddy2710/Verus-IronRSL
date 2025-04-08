use builtin::*;
use builtin_macros::*;
use vstd::{map::*, modes::*, prelude::*, seq::*, seq_lib::*, *};
use vstd::{set::*, set_lib::*};
use crate::protocol::RSL::configuration::*;
use crate::protocol::RSL::constants::*;
use crate::protocol::RSL::broadcast::*;
use crate::protocol::RSL::environment::*;
use crate::protocol::RSL::types::*;
use crate::protocol::RSL::message::*;
use crate::protocol::common::upper_bound::LeqUpperBound;
use crate::common::framework::environment_s::*;
use crate::common::native::io_s::*;
use crate::common::collections::count_matches::*;


verus! {
    pub struct LAcceptor {
        pub constants:LReplicaConstants,
        pub max_bal:Ballot,
        pub votes:Votes,
        pub last_checkpointed_operation:Seq<OperationNumber>,
        pub log_truncation_point:OperationNumber,
    }

    pub open spec fn IsLogTruncationPointValid(log_truncation_point:OperationNumber, last_checkpointed_operation:Seq<OperationNumber>,
                                              config:LConfiguration) -> bool
    {
        IsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, LMinQuorumSize(config))
    }

    pub open spec fn RemoveVotesBeforeLogTruncationPoint(votes:Votes, votes_:Votes, log_truncation_point:OperationNumber) -> bool
    {
        
    }

    pub open spec fn LAddVoteAndRemoveOldOnes(votes:Votes, votes_:Votes, new_opn:OperationNumber, new_vote:Vote, log_truncation_point:OperationNumber) -> bool
    {
       
    }

    pub open spec fn LAcceptorInit(a:LAcceptor, c:LReplicaConstants) -> bool
    {
        
    }

    pub open spec fn LAcceptorProcess1a(
        s: LAcceptor, 
        s_: LAcceptor, 
        inp: RslPacket, 
        sent_packets: Seq<RslPacket>
    ) -> bool
        recommends
            inp.msg is RslMessage1a,
    {
        
    }

    pub open spec fn LAcceptorProcess2a(
        s: LAcceptor, 
        s_: LAcceptor, 
        inp: RslPacket, 
        sent_packets: Seq<RslPacket>
    ) -> bool
        recommends
            inp.msg is RslMessage2a,
            s.constants.all.config.replica_ids.contains(inp.src),
            BalLeq(s.max_bal, inp.msg->bal_2a),
            LeqUpperBound(inp.msg->opn_2a, s.constants.all.params.max_integer_val)
    {
        
    }

    pub open spec fn LAcceptorProcessHeartbeat(
        s: LAcceptor, 
        s_: LAcceptor, 
        inp: RslPacket
    ) -> bool
        recommends 
            inp.msg is RslMessageHeartbeat
    {
        
    }

    pub open spec fn LAcceptorTruncateLog(
        s: LAcceptor, 
        s_: LAcceptor, 
        opn: OperationNumber
    ) -> bool
    {
        
    }
}