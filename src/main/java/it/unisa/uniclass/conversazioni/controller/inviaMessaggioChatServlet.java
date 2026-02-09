package it.unisa.uniclass.conversazioni.controller;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.ejb.EJB;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;
import java.time.LocalDateTime;
import java.util.List;

@WebServlet(name = "inviaMessaggioChat", value = "/inviaMessaggioChatServlet")
public class inviaMessaggioChatServlet extends HttpServlet {

    @EJB
    //@ spec_public
    //@ nullable
    private MessaggioService messaggioService;

    @EJB
    //@ spec_public
    //@ nullable
    private AccademicoService accademicoService;

    /**
     * Setter per iniettare il MessaggioService (utile per i test).
     * @param messaggioService il service da iniettare
     */
    //@ requires messaggioService != null;
    //@ ensures this.messaggioService == messaggioService;
    public void setMessaggioService(MessaggioService messaggioService) {
        this.messaggioService = messaggioService;
    }

    /**
     * Setter per iniettare l'AccademicoService (utile per i test).
     * @param accademicoService il service da iniettare
     */
    //@ requires accademicoService != null;
    //@ ensures this.accademicoService == accademicoService;
    public void setAccademicoService(AccademicoService accademicoService) {
        this.accademicoService = accademicoService;
    }

    /**
     * Gestisce le richieste GET per inviare un messaggio in chat.
     * @param request la richiesta HTTP
     * @param response la risposta HTTP
     */
    //@ requires request != null;
    //@ requires response != null;
    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        try {
            HttpSession session = request.getSession();

            // Email attuale (autore del messaggio)
            String emailSession = (String) session.getAttribute("utenteEmail");

            // Email di destinazione
            String emailDest = request.getParameter("emailInvio");
            System.out.println("lo sto inviando a :" + emailDest);

            // Messaggio da inviare
            String messaggio = request.getParameter("testo");

            System.out.println("guarda che mssaggio:" + messaggio);


            Accademico accademicoSelf = accademicoService.trovaEmailUniClass(emailSession);
            Accademico accademicoDest = accademicoService.trovaEmailUniClass(emailDest);


            Topic top = new Topic();
            top.setCorsoLaurea(accademicoSelf.getCorsoLaurea());
            top.setNome("VUOTO");

            // Crea un nuovo messaggio
            Messaggio messaggio1 = new Messaggio();
            messaggio1.setAutore(accademicoSelf);
            messaggio1.setDestinatario(accademicoDest);
            messaggio1.setBody(messaggio);
            messaggio1.setDateTime(LocalDateTime.now());
            messaggio1.setTopic(top);


            // Salva il messaggio
            messaggioService.aggiungiMessaggio(messaggio1);


            List<Messaggio> messaggi = messaggioService.trovaTutti();

            request.setAttribute("messaggi", messaggi);
            request.setAttribute("accademici", messaggioService.trovaMessaggeriDiUnAccademico(accademicoSelf.getMatricola()));
            response.sendRedirect("chatServlet?accademico="+accademicoDest.getEmail()+"&accademicoSelf="+accademicoSelf.getEmail());
        } catch (IOException e) {
            request.getServletContext().log("Error processing chat message request", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                request.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    /**
     * Gestisce le richieste POST delegando al metodo doGet.
     * @param request la richiesta HTTP
     * @param response la risposta HTTP
     */
    //@ requires request != null;
    //@ requires response != null;
    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}

