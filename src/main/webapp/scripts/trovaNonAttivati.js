
function aggiornaListaUtenti() {
    var contextPath = window.location.pathname.substring(0, window.location.pathname.indexOf("/", 1));
    var url = contextPath + "/GetNonAttivati";
    var url2 = contextPath + "/GetAttivati";
    var xhr = new XMLHttpRequest();
    var xhrr = new XMLHttpRequest();

    xhr.open("GET", url, true);
    xhr.onload = function () {
        if (xhr.status === 200) {

            var response = JSON.parse(xhr.responseText);
            console.log(response);


            var listContainer = document.querySelector('.list');
            listContainer.innerHTML = '';


            response.forEach(function (utente) {

                const p1 = document.createElement('p');
                const p2 = document.createElement('p')
                const p3 = document.createElement('p')
                p1.textContent = `Matricola: ${utente["matricola"]}`
                p2.textContent = `Email: ${utente['email']}`
                p3.textContent = `Tipo: ${utente["tipo"]}`

                listContainer.appendChild(p1)
                listContainer.appendChild(p2)
                listContainer.appendChild(p3)
                
            });
        } else {
            console.error("Errore nella richiesta AJAX: " + xhr.status);
        }
    };


    xhrr.open("GET", url2, true);
    xhrr.onload = function () {
        if (xhrr.status === 200) {
            var response = JSON.parse(xhrr.responseText);
            console.log(response);

            // Debug: Verifica se l'elemento select è trovato
            var emailSelect = document.getElementById("email-remove");
            if (!emailSelect) {
                console.error("Elemento 'select' non trovato.");
                return;
            }


            var emailSelect = document.getElementById("email-remove");
            emailSelect.innerHTML = '<option value="">-- Seleziona un\'email --</option>';

            response.forEach(function (utente) {
                var option = document.createElement('option');
                option.value = utente["email"];
                option.textContent = utente["email"];

                emailSelect.appendChild(option);
            });
        } else {
            console.error("Errore nella richiesta AJAX: " + xhrr.status);
        }
    };


    xhrr.send();
    xhr.send();
}


window.onload = function() {
    aggiornaListaUtenti();
};
