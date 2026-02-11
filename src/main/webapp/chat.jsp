<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente" %>
<%@ page import="it.unisa.uniclass.utenti.model.Accademico" %>
<%@ page import="it.unisa.uniclass.utenti.model.Ruolo" %>
<%@ page import="it.unisa.uniclass.conversazioni.model.Messaggio" %>
<%@ page import="it.unisa.uniclass.conversazioni.model.Topic" %>
<%@ page import="java.util.List" %>
<%@ page import="java.util.ArrayList" %>

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
            Chat con: <%= interlocutore.getNome() %> <%= interlocutore.getCognome() %>
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
            <span class="message-text">[<%= t.getNome() %>]</span>
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
            <span class="message-text"><%= messaggio.getBody() %></span>
        </div>
        <%
                }
            }
        %>
    </div>

    <div class="chat-input-container">
        <input type="text" id="testo" name="testo" class="chat-input" placeholder="Scrivi un messaggio..." required>

        <% if (interlocutore != null) { %>
        <input type="hidden" id="emailInvio" name="emailInvio" value="<%= interlocutore.getEmail() %>">
        <% } %>

        <button type="button" class="send-button" onclick="sendMessage()">Invia</button>
    </div>
</div>

<script>
    function sendMessage() {
        var testo = document.getElementById('testo').value;
        var emailInvioElem = document.getElementById('emailInvio');

        if (!emailInvioElem) {
            alert("Nessun destinatario selezionato");
            return;
        }

        var email = emailInvioElem.value;
        if (testo.trim() !== "") {
            window.location.href = 'inviaMessaggioChatServlet?testo=' +
                encodeURIComponent(testo) + '&emailInvio=' + encodeURIComponent(email);
        }
    }
</script>

</body>
</html>
