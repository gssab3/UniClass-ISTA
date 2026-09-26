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

                var restoSelect = document.getElementById("resto");
                restoSelect.innerHTML = '<option value="">-- Seleziona un resto --</option>';

                response.forEach(function(resto) {
                    const option = new Option(resto.nome, resto.nome)
                    restoSelect.appendChild(option)
                });
            }
        };

        // --- ANNI ---
        var xhrr = new XMLHttpRequest();
        xhrr.open("GET", contextPath + "/getAnno?corsoLaurea=" + encodeURIComponent(corsoLaurea), true);

        xhrr.onload = function() {
            if (xhrr.status === 200) {
                var response = JSON.parse(xhrr.responseText);
                var annoSelect = document.getElementById("anno");

                annoSelect.replaceChildren(new Option("-- Seleziona un anno --", ""));
                response.forEach(function (anno) {
                    annoSelect.appendChild(new Option(anno.nome, anno.nome));
                });
            }
        };

        // Invia le richieste
        xhr.send();
        xhrr.send();
    }
}
