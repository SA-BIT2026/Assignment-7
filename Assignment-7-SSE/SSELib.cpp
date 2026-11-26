/**
 * SSELib.cpp
 * @author kisslune
 */

#include "SSEHeader.h"
#include "Util/Options.h"

using namespace SVF;
using namespace SVFUtil;
using namespace llvm;
using namespace z3;

/// Traverse the ICFG from the program entry to each assertion. A call opens a
/// new scope in the visited set so the same callee can be walked again from a
/// different call site, and a return is only taken when it matches the call at
/// the top of the stack. This avoids the bogus cross-call paths that a plain
/// "no repeated node" walk would produce.
void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* snk) {
    const ICFGNode* curNode = curEdge->getDstNode();
    if (curNode == nullptr)
        return;

    // Key the visited set on (edge, callstack) so a call/return cycle in one
    // context does not block the same edge in a different context, while a
    // plain loop inside one activation is still cut off.
    ICFGEdgeStackPair key(curEdge, callstack);
    if (visited.find(key) != visited.end())
        return;
    visited.insert(key);

    path.push_back(curEdge);

    if (curNode == snk)
    {
        collectAndTranslatePath();
        path.pop_back();
        return;
    }

    bool openedCall = false;
    bool closedRet = false;
    if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(curEdge))
    {
        callstack.push_back(callEdge->getCallSite());
        openedCall = true;
    }
    else if (const RetCFGEdge* retEdge = SVFUtil::dyn_cast<RetCFGEdge>(curEdge))
    {
        const CallICFGNode* retCall = retEdge->getCallSite();
        if (callstack.empty() || callstack.back() != retCall)
        {
            path.pop_back();
            return;
        }
        callstack.pop_back();
        closedRet = true;
    }

    for (const ICFGEdge* next : curNode->getOutEdges())
        reachability(next, snk);

    if (openedCall)
        callstack.pop_back();
    else if (closedRet)
        callstack.push_back(SVFUtil::cast<RetCFGEdge>(curEdge)->getCallSite());

    path.pop_back();
}

/// Translate every collected path, verify its assertion, and restore the
/// solver for the next path.
void SSE::collectAndTranslatePath() {
    paths.insert(z3Mgr->callingCtxToStr(callingCtx));
    if (translatePath(path) == false)
        return;
    assertchecking(path.back()->getDstNode());
    resetSolver();
}

/// Enter a callee: remember the call site for both context-sensitive variable
/// naming and call/return matching, then bind actual arguments to formals.
void SSE::handleCall(const CallCFGEdge* calledge) {
    const CallICFGNode* cs = calledge->getCallSite();

    // The actual argument lives in the caller context, the formal parameter
    // in the callee context, so read the two sides on opposite sides of push.
    for (const CallPE* callPE : calledge->getCallPEs())
    {
        expr actual = getZ3Expr(callPE->getRHSVarID());
        pushCallingCtx(cs);
        expr formal = getZ3Expr(callPE->getLHSVarID());
        popCallingCtx();
        addToSolver(formal == actual);
    }
    pushCallingCtx(cs);
}

/// Leave a callee: restore the caller context and pass the return value back.
void SSE::handleRet(const RetCFGEdge* retEdge) {
    const RetPE* retPE = retEdge->getRetPE();
    if (retPE != nullptr)
    {
        // The returned value belongs to the callee context; the receiving
        // variable belongs to the caller context.
        expr returned = getZ3Expr(retPE->getRHSVarID());
        popCallingCtx();
        expr received = getZ3Expr(retPE->getLHSVarID());
        addToSolver(received == returned);
    }
    else
        popCallingCtx();
}

/// A conditional edge is feasible only when the branch condition equals the
/// value that selects this successor. Ask Z3 before continuing so dead paths
/// are dropped early.
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    const SVFVar* condVar = edge->getCondition();
    if (condVar == nullptr)
        return true;

    expr cond = getZ3Expr(condVar->getId());
    expr expected = getCtx().int_val(static_cast<int>(edge->getSuccessorCondValue()));
    addToSolver(cond == expected);
    return getSolver().check() != z3::unsat;
}

/// Translate the statements attached to the destination node of an edge.
bool SSE::handleNonBranch(const IntraCFGEdge* edge) {
    const ICFGNode* dstNode = edge->getDstNode();
    const ICFGNode* srcNode = edge->getSrcNode();
    DBOP(if(!SVFUtil::isa<CallICFGNode>(dstNode) && !SVFUtil::isa<RetICFGNode>(dstNode)) std::cout << "\n## Analyzing "<< dstNode->toString() << "\n");

    for (const SVFStmt *stmt : dstNode->getSVFStmts())
    {
        if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            expr lhs = getZ3Expr(addr->getLHSVarID());
            expr rhs = getMemObjAddress(addr->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            expr lhs = getZ3Expr(copy->getLHSVarID());
            expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            expr lhs = getZ3Expr(load->getLHSVarID());
            expr ptr = getZ3Expr(load->getRHSVarID());
            addToSolver(lhs == z3Mgr->loadValue(ptr));
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            expr val = getZ3Expr(store->getRHSVarID());
            expr ptr = getZ3Expr(store->getLHSVarID());
            z3Mgr->storeValue(ptr, val);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            expr lhs = getZ3Expr(gep->getLHSVarID());
            expr ptr = getZ3Expr(gep->getRHSVarID());
            s32_t offset = z3Mgr->getGepOffset(gep, callingCtx);
            addToSolver(lhs == z3Mgr->getGepObjAddress(ptr, offset));
        }
        /// Given a CmpStmt "r = a > b"
        /// cmp->getOpVarID(0)/cmp->getOpVarID(1) returns the first/second operand, i.e., "a" and "b"
        /// cmp->getResID() returns the result operand "r" and cmp->getPredicate() gives you the predicate ">"
        /// Find the comparison predicates in "class CmpStmt:Predicate" under SVF/svf/include/SVFIR/SVFStatements.h
        /// You are only required to handle integer predicates, including ICMP_EQ, ICMP_NE, ICMP_UGT, ICMP_UGE, ICMP_ULT, ICMP_ULE, ICMP_SGT, ICMP_SGE, ICMP_SLE, ICMP_SLT
        /// We assume integer-overflow-free in this assignment
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            expr op0 = getZ3Expr(cmp->getOpVarID(0));
            expr op1 = getZ3Expr(cmp->getOpVarID(1));
            expr res = getZ3Expr(cmp->getResID());
            switch (cmp->getPredicate())
            {
                case CmpStmt::ICMP_EQ: addToSolver(res == ite(op0 == op1, getCtx().int_val(1), getCtx().int_val(0))); break;
                case CmpStmt::ICMP_NE: addToSolver(res == ite(op0 != op1, getCtx().int_val(1), getCtx().int_val(0))); break;
                case CmpStmt::ICMP_UGT:
                case CmpStmt::ICMP_SGT: addToSolver(res == ite(op0 > op1, getCtx().int_val(1), getCtx().int_val(0))); break;
                case CmpStmt::ICMP_UGE:
                case CmpStmt::ICMP_SGE: addToSolver(res == ite(op0 >= op1, getCtx().int_val(1), getCtx().int_val(0))); break;
                case CmpStmt::ICMP_ULT:
                case CmpStmt::ICMP_SLT: addToSolver(res == ite(op0 < op1, getCtx().int_val(1), getCtx().int_val(0))); break;
                case CmpStmt::ICMP_ULE:
                case CmpStmt::ICMP_SLE: addToSolver(res == ite(op0 <= op1, getCtx().int_val(1), getCtx().int_val(0))); break;
                default: assert(false && "unsupported CmpStmt predicate");
            }
        }
        else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
        {
            expr op0 = getZ3Expr(binary->getOpVarID(0));
            expr op1 = getZ3Expr(binary->getOpVarID(1));
            expr res = getZ3Expr(binary->getResID());
            switch (binary->getOpcode())
            {
                case BinaryOperator::Add:
                    addToSolver(res == op0 + op1);
                    break;
                case BinaryOperator::Sub:
                    addToSolver(res == op0 - op1);
                    break;
                case BinaryOperator::Mul:
                    addToSolver(res == op0 * op1);
                    break;
                case BinaryOperator::SDiv:
                    addToSolver(res == op0 / op1);
                    break;
                case BinaryOperator::SRem:
                    addToSolver(res == op0 % op1);
                    break;
                case BinaryOperator::Xor:
                    addToSolver(res == bv2int(int2bv(32, op0) ^ int2bv(32, op1), 1));
                    break;
                case BinaryOperator::And:
                    addToSolver(res == bv2int(int2bv(32, op0) & int2bv(32, op1), 1));
                    break;
                case BinaryOperator::Or:
                    addToSolver(res == bv2int(int2bv(32, op0) | int2bv(32, op1), 1));
                    break;
                case BinaryOperator::AShr:
                    addToSolver(res == bv2int(ashr(int2bv(32, op0), int2bv(32, op1)), 1));
                    break;
                case BinaryOperator::Shl:
                    addToSolver(res == bv2int(shl(int2bv(32, op0), int2bv(32, op1)), 1));
                    break;
                default:
                    assert(false && "implement this part");
            }
        }
        else if (const BranchStmt *br = SVFUtil::dyn_cast<BranchStmt>(stmt))
        {
            DBOP(std::cout << "\t skip handled when traversal Conditional IntraCFGEdge \n");
        }
        else if (const SelectStmt *select = SVFUtil::dyn_cast<SelectStmt>(stmt)) {
            expr res = getZ3Expr(select->getResID());
            expr tval = getZ3Expr(select->getTrueValue()->getId());
            expr fval = getZ3Expr(select->getFalseValue()->getId());
            expr cond = getZ3Expr(select->getCondition()->getId());
            addToSolver(res == ite(cond == getCtx().int_val(1), tval, fval));
        }
        else if (const PhiStmt *phi = SVFUtil::dyn_cast<PhiStmt>(stmt)) {
            expr res = getZ3Expr(phi->getResID());
            bool opINodeFound = false;
            for(u32_t i = 0; i < phi->getOpVarNum(); i++){
                assert(srcNode && "we don't have a predecessor ICFGNode?");
                if (srcNode->getFun()->postDominate(srcNode->getBB(),phi->getOpICFGNode(i)->getBB()))
                {
                    expr ope = getZ3Expr(phi->getOpVar(i)->getId());
                    addToSolver(res == ope);
                    opINodeFound = true;
                }
            }
            assert(opINodeFound && "predecessor ICFGNode of this PhiStmt not found?");
        }
    }

    return true;
}

/// Traverse each program path
bool SSE::translatePath(std::vector<const ICFGEdge*>& path) {
    for (const ICFGEdge* edge : path) {
        if (const IntraCFGEdge* intraEdge = SVFUtil::dyn_cast<IntraCFGEdge>(edge)) {
            if (handleIntra(intraEdge) == false)
                return false;
        }
        else if (const CallCFGEdge* call = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {
            handleCall(call);
        }
        else if (const RetCFGEdge* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
            handleRet(ret);
        }
        else
            assert(false && "what other edges we have?");
    }

    return true;
}

/// Program entry
void SSE::analyse() {
    for (const ICFGNode* src : identifySources()) {
        assert(SVFUtil::isa<GlobalICFGNode>(src) && "reachability should start with GlobalICFGNode!");
        for (const ICFGNode* sink : identifySinks()) {
            const IntraCFGEdge startEdge(nullptr, const_cast<ICFGNode*>(src));
            // Visited edges are only valid for one sink: clearing them here
            // lets the next assertion see all paths from the entry again.
            visited.clear();
            /// start traversing from the entry to each assertion and translate each path
            reachability(&startEdge, sink);
            resetSolver();
        }
    }
}
