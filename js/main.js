//wait for DOM to load and parse
window.addEventListener('DOMContentLoaded', (event) => {
    const connectButton = document.getElementById("connect");

    let zilliqa = null;
    let crypto = null;

    //check for connect button click
    connectButton.addEventListener('click', function () {
        if (typeof window.zilPay !== 'undefined') {
            return zilPay.wallet.connect().then(function (accounts) {
                zilliqa = window.zilPay;
                crypto = zilPay.crypto;

                $('#connect').fadeOut(600);
                $('#tokenForm').delay(500).fadeIn(600);
                $('#blob').width('200%');
            })
        } else {
            alert("Couldn't find zilPay");
        }
    });
});