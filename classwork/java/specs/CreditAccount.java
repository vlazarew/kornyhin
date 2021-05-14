/*@
    predicate CreditAccount_is_correct(CreditAccount a) =
        a.credit >= 0 && a.balance >= -a.credit;
*/

public class CreditAccount extends Account
{
    private int credit;

    /*@
        requires \valid(this);
        requires credit >= 0;
        ensures CreditAccount_is_correct(this);
        ensures this.balance == 0;
        ensures this.credit == credit;
    */
    public CreditAccount(int credit) {
        super();
        this.credit = credit;
    }

    /*@
        requires \valid(this);
        requires CreditAccount_is_correct(this);
        ensures \result == credit;
    */
    public int getCredit() {
        return credit;
    }

    /*@
        requires \valid(this);
        requires CreditAccount_is_correct(this);
        requires value > 0;
        assigns balance; //!!!!!!!
        ensures CreditAccount_is_correct(this);
        ensures \old(balance) >= value - credit && balance == \old(balance) - value;
        signals (NotEnoughBalance e)
            \old(balance) < value - credit &&
            \old(balance) == balance;
    */
    public void withdraw(int value) throws NotEnoughBalance {
        int balance = getBalance();
        if (balance >= value - credit) {
            this.balance = balance - value;
        } else {
            throw new NotEnoughBalance();
        }
    }

/* ****************************************

    // methods getBalance() and deposit() are inherited
    // but they have another specification in this class!

    /@
        requires \valid(this);
        requires CreditAccount_is_correct(this);
        ensures \result == balance;
    /
    public int getBalance() {
        return balance;
    }

    /@
        requires \valid(this);
        requires CreditAccount_is_correct(this);
        requires value > 0;
        assigns balance; //!!!!!!!
        ensures CreditAccount_is_correct(this);
        ensures balance == \old(balance) + value;
    /
    public void deposit(int value) {
        balance += value;
    }
** ****************************************** */
}
