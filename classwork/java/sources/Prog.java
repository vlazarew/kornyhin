public class Prog
{
    public static void move(Account from, Account to, int value)
        throws Account.NotEnoughBalance
    {
        if (from != to) {
            from.withdraw(value);
            to.deposit(value);
        }
    }

    public static void main(String[] args)
    {
        Account a1 = new Account();
        Account a2 = new Account();
        Account a3 = new CreditAccount(100);
        CreditAccount a4 = new CreditAccount(10);

        try {
            a1.deposit(100);
            move(a1, a2, 10);
            int b1 = a1.getBalance();
            int b2 = a2.getBalance();
            //@ assert b1 == 90;
            //@ assert b2 == 10;
        } catch (Account.NotEnoughBalance e) {
            //@ assert \false;
        }

        try {
            move(a1, a3, 10);
            int b3 = a1.getBalance();
            int b4 = a3.getBalance();
            int b5 = a2.getBalance();
            //@ assert b3 == 80;
            //@ assert b4 == 10;
            //@ assert b5 == 10;
        } catch (Account.NotEnoughBalance e) {
            //@ assert \false;
        }
    }
}
