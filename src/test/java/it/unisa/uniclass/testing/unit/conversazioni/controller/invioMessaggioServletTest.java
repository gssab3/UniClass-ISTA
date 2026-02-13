package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.controller.invioMessaggioServlet;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.ServletContext;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class invioMessaggioServletTest {

    private invioMessaggioServlet servlet;

    @Mock private HttpServletRequest request;
    @Mock private HttpServletResponse response;
    @Mock private HttpSession session;
    @Mock private ServletContext servletContext;
    @Mock private MessaggioService messaggioService;
    @Mock private UserDirectory userDirectory;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new invioMessaggioServlet();

        Field msgField = invioMessaggioServlet.class.getDeclaredField("messaggioService");
        msgField.setAccessible(true);
        msgField.set(servlet, messaggioService);

        Field userField = invioMessaggioServlet.class.getDeclaredField("userDirectory");
        userField.setAccessible(true);
        userField.set(servlet, userDirectory);

        lenient().when(request.getSession()).thenReturn(session);
        lenient().when(request.getServletContext()).thenReturn(servletContext);
    }

    @Test
    @DisplayName("DoGet: Invio Messaggio con Topic")
    void testDoGet_WithTopic() throws IOException {

        String emailSelf = "me@unisa.it";
        String emailDest = "dest@unisa.it";
        String testo = "Hello";
        String topicName = "Info Esame";

        when(session.getAttribute("utenteEmail")).thenReturn(emailSelf);
        when(request.getParameter("email")).thenReturn(emailDest);
        when(request.getParameter("testo")).thenReturn(testo);
        when(request.getParameter("topic")).thenReturn(topicName);

        Accademico self = new Accademico();
        self.setMatricola("123");
        self.setCorsoLaurea(new CorsoLaurea());

        Accademico dest = new Accademico();

        when(userDirectory.getAccademico(emailSelf)).thenReturn(self);
        when(userDirectory.getAccademico(emailDest)).thenReturn(dest);

        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico("123")).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());

        Messaggio capturedMsg = captor.getValue();
        assertEquals(testo, capturedMsg.getBody());
        assertNotNull(capturedMsg.getTopic());
        assertEquals(topicName, capturedMsg.getTopic().getNome());

        verify(response).sendRedirect("Conversazioni");
    }

    @Test
    @DisplayName("DoGet: Invio Messaggio senza Topic")
    void testDoGet_NoTopic() throws IOException {

        when(session.getAttribute("utenteEmail")).thenReturn("a@a.it");
        when(request.getParameter("email")).thenReturn("b@b.it");
        when(request.getParameter("testo")).thenReturn("ciao");
        when(request.getParameter("topic")).thenReturn("");

        Accademico self = new Accademico();
        self.setMatricola("999"); // IMPORTANTISSIMO per evitare NPE
        self.setCorsoLaurea(new CorsoLaurea());

        Accademico dest = new Accademico();

        when(userDirectory.getAccademico("a@a.it")).thenReturn(self);
        when(userDirectory.getAccademico("b@b.it")).thenReturn(dest);

        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico("999")).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());

        Messaggio msg = captor.getValue();
        assertNull(msg.getTopic());

        verify(response).sendRedirect("Conversazioni");
    }

    @Test
    @DisplayName("DoGet: Utente non trovato -> Errore 500")
    void testDoGet_UsersNotFound() throws IOException {

        when(session.getAttribute("utenteEmail")).thenReturn("me");
        when(request.getParameter("email")).thenReturn("you");

        when(userDirectory.getAccademico("me")).thenReturn(new Accademico());
        when(userDirectory.getAccademico("you")).thenReturn(null);

        servlet.doGet(request, response);

        verify(messaggioService, never()).aggiungiMessaggio(any());
        verify(servletContext).log(eq("Error sending message"), any(Exception.class));
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }

    @Test
    @DisplayName("DoGet: Eccezione generica -> catch branch")
    void testDoGet_RuntimeException() throws IOException {

        when(request.getSession()).thenThrow(new RuntimeException("Boom"));

        servlet.doGet(request, response);

        verify(servletContext).log(eq("Error sending message"), any(RuntimeException.class));
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }

    @Test
    @DisplayName("DoPost: Delega a DoGet")
    void testDoPost() throws ServletException, IOException {

        when(request.getSession()).thenThrow(new RuntimeException("Delegation"));

        servlet.doPost(request, response);

        verify(servletContext).log(eq("Error sending message"), any(RuntimeException.class));
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }
}
