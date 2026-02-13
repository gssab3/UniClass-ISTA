package it.unisa.uniclass.testing.unit.utenti.service;


import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectoryImpl;
import it.unisa.uniclass.utenti.service.UtenteService;
import org.junit.jupiter.api.Test;


import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class UserDirectoryTest {

    @Test
    void getUser_shouldReturnUser_whenFound() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        Utente u = new Utente();
        when(service.getUtenteByEmail("x")).thenReturn(u);

        assertEquals(u, dir.getUser("x"));
    }

    @Test
    void getUser_shouldReturnNull_whenNotFound() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        when(service.getUtenteByEmail("x")).thenThrow(new NotFoundUserException(""));

        assertNull(dir.getUser("x"));
    }

    @Test
    void getAccademico_shouldReturnAccademico_whenUserIsAccademico() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        Accademico a = new Accademico();
        when(service.getUtenteByEmail("x")).thenReturn(a);

        assertEquals(a, dir.getAccademico("x"));
    }

    @Test
    void getAccademico_shouldReturnNull_whenUserIsNotAccademico() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        when(service.getUtenteByEmail("x")).thenReturn(new Utente());

        assertNull(dir.getAccademico("x"));
    }

    @Test
    void getAccademico_shouldReturnNull_whenUserNotFound() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        when(service.getUtenteByEmail("x")).thenThrow(new NotFoundUserException(""));

        assertNull(dir.getAccademico("x"));
    }

    @Test
    void isDocente_shouldReturnTrue_whenAccademicoDocente() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        Accademico a = new Accademico();
        a.setRuolo(Ruolo.DOCENTE);

        when(service.getUtenteByEmail("x")).thenReturn(a);

        assertTrue(dir.isDocente("x"));
    }

    @Test
    void isDocente_shouldReturnFalse_whenAccademicoNotDocente() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        Accademico a = new Accademico();
        a.setRuolo(Ruolo.STUDENTE);

        when(service.getUtenteByEmail("x")).thenReturn(a);

        assertFalse(dir.isDocente("x"));
    }

    @Test
    void isDocente_shouldReturnFalse_whenNotAccademico() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        when(service.getUtenteByEmail("x")).thenReturn(new Utente());

        assertFalse(dir.isDocente("x"));
    }

    @Test
    void isStudente_shouldReturnTrue_whenAccademicoStudente() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        Accademico a = new Accademico();
        a.setRuolo(Ruolo.STUDENTE);

        when(service.getUtenteByEmail("x")).thenReturn(a);

        assertTrue(dir.isStudente("x"));
    }

    @Test
    void isCoordinatore_shouldReturnTrue_whenAccademicoCoordinatore() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        Accademico a = new Accademico();
        a.setRuolo(Ruolo.COORDINATORE);

        when(service.getUtenteByEmail("x")).thenReturn(a);

        assertTrue(dir.isCoordinatore("x"));
    }

    @Test
    void cambiaStatoAttivazione_shouldDoNothing_whenUserNotFound() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        when(service.getUtenteByEmail("x")).thenThrow(new NotFoundUserException(""));

        dir.cambiaStatoAttivazione("x", true);

        verify(service, never()).aggiornaUtente(any());
    }

    @Test
    void cambiaStatoAttivazione_shouldDoNothing_whenUserNotAccademico() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        when(service.getUtenteByEmail("x")).thenReturn(new Utente());

        dir.cambiaStatoAttivazione("x", true);

        verify(service, never()).aggiornaUtente(any());
    }

    @Test
    void cambiaStatoAttivazione_shouldUpdateAccademico_whenValid() throws Exception {
        UtenteService service = mock(UtenteService.class);
        UserDirectoryImpl dir = new UserDirectoryImpl(service);

        Accademico a = new Accademico();
        when(service.getUtenteByEmail("x")).thenReturn(a);

        dir.cambiaStatoAttivazione("x", true);

        assertTrue(a.isAttivato());
        verify(service).aggiornaUtente(a);
    }
}
