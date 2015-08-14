public class TestJMLContracts {
	public final int OVERDRAFT_LIMIT = 0;

	/*@ public invariant this.balance >= OVERDRAFT_LIMIT; */
	public int balance = 0;
	
	/*@ public invariant FM.FeatureModel.bankaccount && (! (FM.FeatureModel.dailylimit || FM.FeatureModel.interest || FM.FeatureModel.overdraft || FM.FeatureModel.logging || FM.FeatureModel.creditworthiness || FM.FeatureModel.lock) || FM.FeatureModel.bankaccount) && (! FM.FeatureModel.interestestimation || FM.FeatureModel.interest) && (! FM.FeatureModel.transactionlog || FM.FeatureModel.logging) && (! FM.FeatureModel.transaction || FM.FeatureModel.lock) && (FM.FeatureModel.logging && FM.FeatureModel.transaction == FM.FeatureModel.transactionlog);@*/
	/*@ accessible \inv: balance; @*/

	
	/*@
	 @ ensures balance == 0;
	 @ assignable \nothing;
	 @*/
	TestJMLContracts() {
	}
	
	/*@
	 @ requires x != 0;
	 @ ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) + x);
	 @ assignable balance; 
	 @*/
	boolean update(int x) {
		int newBalance = balance + x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = balance + x;
		return true;
	}

	/*@ requires x != 0;
	 @  ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) - x);
	 @ assignable balance;
	 @*/
	boolean undoUpdate(int x) {
		int newBalance = balance - x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}
	
}