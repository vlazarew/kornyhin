/*@
    predicate Account_is_correct(Account a) =
        a.balance >= 0
*/

public class Account
{
    public class NotEnoughBalance extends Exception
    {
    }

    private int balance;

    /*@
        requires \valid(this);
        ensures Account_is_correct(this) && balance == 0;
    */
    public Account() {
        balance = 0;
    }

    /*@
        requires \valid(this);
        requires Account_is_correct(this);
        ensures \result == balance;
    */
    public int getBalance() {
        return balance;
    }

    /*@
        requires \valid(this);
        requires Account_is_correct(this);
        requires value > 0;
        assigns balance; //!!!!!!!
        ensures Account_is_correct(this);
        ensures balance == \old(balance) + value;
    */
    public void deposit(int value) {
        balance += value;
    }

    /*@
        requires \valid(this);
        requires Account_is_correct(this);
        requires value > 0;
        assigns balance; //!!!!!!!
        ensures Account_is_correct(this);
        ensures \old(balance) >= value && balance == \old(balance) - value;
        signals (NotEnoughBalance e)
            \old(balance) < value && balance == \old(balance);
    */
    public void withdraw(int value) throws NotEnoughBalance {
        if (balance >= value) {
            balance -= value;
        } else {
            throw new NotEnoughBalance();
        }
    }
}
