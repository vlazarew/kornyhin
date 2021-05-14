public class Account
{
    public class NotEnoughBalance extends Exception
    {
    }

    private int balance;

    public Account() {
        balance = 0;
    }

    public int getBalance() {
        return balance;
    }

    public void deposit(int value) {
        balance += value;
    }

    public void withdraw(int value) throws NotEnoughBalance {
        if (balance >= value) {
            balance -= value;
        } else {
            throw new NotEnoughBalance();
        }
    }
}
