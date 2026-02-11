// Funzione per aggiornare il resto e l'anno in base alla selezione del corso di laurea
function aggiornaResto() {
    var corsoLaurea = document.getElementById("corsoLaurea").value;

    if (corsoLaurea) {

        // --- RESTI ---
        var xhr = new XMLHttpRequest();
        xhr.open("GET", contextPath + "/getResto?corsoLaurea=" + encodeURIComponent(corsoLaurea), true);

        xhr.onload = function() {
            if (xhr.status === 200) {
                var response = JSON.parse(xhr.responseText);

                console.log("RESTI:", response);

                var restoSelect = document.getElementById("resto");
                restoSelect.innerHTML = '<option value="">-- Seleziona un resto --</option>';

                response.forEach(function(resto) {
                    restoSelect.innerHTML += `<option value="${resto.nome}">${resto.nome}</option>`;
                });
            }
        };

        // --- ANNI ---
        var xhrr = new XMLHttpRequest();
        xhrr.open("GET", contextPath + "/getAnno?corsoLaurea=" + encodeURIComponent(corsoLaurea), true);

        xhrr.onload = function() {
            if (xhrr.status === 200) {
                var response = JSON.parse(xhrr.responseText);

                console.log("ANNI:", response);

                var annoSelect = document.getElementById("anno");
                annoSelect.innerHTML = '<option value="">-- Seleziona un anno --</option>';

                response.forEach(function(anno) {
                    annoSelect.innerHTML += `<option value="${anno.nome}">${anno.nome}</option>`;
                });
            }
        };

        // Invia le richieste
        xhr.send();
        xhrr.send();
    }
}
