<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente" %>
<%@ page import="it.unisa.uniclass.utenti.model.Accademico" %>
<%@ page import="it.unisa.uniclass.utenti.model.Ruolo" %>
<%@ page import="it.unisa.uniclass.conversazioni.model.Messaggio" %>
<%@ page import="it.unisa.uniclass.conversazioni.model.Topic" %>
<%@ page import="java.util.List" %>
<%@ page import="java.util.ArrayList" %>
<%@ page import="static it.unisa.uniclass.common.Utils.escapeHTML" %>

<%
    HttpSession sessione = request.getSession(false);
    if (sessione == null || sessione.getAttribute("currentSessionUser") == null) {
        response.sendRedirect("Login.jsp");
        return;
    }

    Utente user = (Utente) sessione.getAttribute("currentSessionUser");

    if (!(user instanceof Accademico)) {
        response.sendRedirect("ErroreAccesso.jsp");
        return;
    }

    Accademico accademicoLoggato = (Accademico) user;

    Accademico interlocutore = (Accademico) request.getAttribute("accademico");
    if (interlocutore == null) {
        interlocutore = (Accademico) session.getAttribute("accademico");
    }

    List<Messaggio> messaggigi = (List<Messaggio>) request.getAttribute("messaggigi");
    if (messaggigi == null) {
        messaggigi = (List<Messaggio>) session.getAttribute("messaggigi");
    }
    if (messaggigi == null) messaggigi = new ArrayList<>();
%>

<!DOCTYPE html>
<html lang="it">
<head>
    <title>UniClass Chat</title>
    <link rel="stylesheet" href="styles/chatCss.css">
</head>

<body>

<div class="chat-container">
    <div class="chat-header">
        <h2>
            <% if (interlocutore != null) { %>
            Chat con: <%= escapeHTML(interlocutore.getNome()) %> <%= escapeHTML(interlocutore.getCognome()) %>
            <% } else { %>
            Seleziona un utente
            <% } %>
        </h2>
    </div>

    <div id="chat-box" class="chat-box">
        <%
            if (interlocutore != null) {
                for (Messaggio messaggio : messaggigi) {

                    Accademico autore = messaggio.getAutore();
                    Accademico dest = messaggio.getDestinatario();
                    Topic t = messaggio.getTopic();

                    // Topic
                    if (t != null && t.getNome() != null && !"VUOTO".equals(t.getNome())) {
        %>
        <div class="message red-text">
            <span class="message-text">[<%= escapeHTML(t.getNome()) %>]</span>
        </div>
        <%
            }

            boolean isAutoreSelf = autore != null &&
                    autore.getEmail() != null &&
                    autore.getEmail().equals(accademicoLoggato.getEmail());

            boolean isAutoreInterlocutore = autore != null &&
                    autore.getEmail() != null &&
                    autore.getEmail().equals(interlocutore.getEmail());

            if (!isAutoreSelf && !isAutoreInterlocutore) continue;

            String cssClass = isAutoreSelf ? "self" : "author";
        %>
        <div class="message <%= cssClass %>">
            <span class="message-text"><%= escapeHTML(messaggio.getBody()) %></span>
        </div>
        <%
                }
            }
        %>
    </div>

    <div class="chat-input-container">
        <input type="text" id="testo" name="testo" class="chat-input" placeholder="Scrivi un messaggio..." required>

        <% if (interlocutore != null) { %>
        <input type="hidden" id="emailInvio" name="emailInvio" value="<%= escapeHTML(interlocutore.getEmail()) %>">
        <input type="hidden" id="csrfToken" name="csrfToken" value="<%= it.unisa.uniclass.common.security.CSRF.getToken(request.getSession(true)) %>">
        <% } %>

        <button type="button" class="send-button" onclick="sendMessage()">Invia</button>
    </div>
</div>

<script>
    function sendMessage() {
        var testo = document.getElementById('testo').value;
        var emailInvioElem = document.getElementById('emailInvio');
        var csrfElem = document.getElementById('csrfToken');

        if (!emailInvioElem) {
            alert("Nessun destinatario selezionato");
            return;
        }

        var email = emailInvioElem.value;
        var csrf = csrfElem ? csrfElem.value : "";
        if (testo.trim() !== "") {
            fetch('inviaMessaggioChatServlet', {
                method: 'POST',
                headers: {'Content-Type': 'application/x-www-form-urlencoded'},
                body: 'testo=' + encodeURIComponent(testo) + '&emailInvio=' + encodeURIComponent(email) + '&csrfToken=' + encodeURIComponent(csrf)
            }).then(function() { location.reload(); });
        }
    }
</script>

</body>
</html>
