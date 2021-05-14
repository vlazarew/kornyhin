public class CreditAccount extends Account
{
    private int credit;

    public CreditAccount(int credit) {
        super();
        this.credit = credit;
    }

    public int getCredit() {
        return credit;
    }

    public void withdraw(int value) throws NotEnoughBalance {
        int balance = getBalance();
        if (balance >= value - credit) {
            this.balance = balance - value;
        } else {
            throw new NotEnoughBalance();
        }
    }
}
